module Hc4 where

import qualified Numeric.Interval as I
import Control.Monad (join)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.State
-- TODO: nub is bad, try something like nub = toList . Set.fromList ? 

type Interval = I.Interval Double
type Box = Map.Map VarId Interval
type VarId = Int

data Term = 
    TConst Double
  | TVar VarId
  | TAdd Term Term
  | TSub Term Term
  | TMul Term Term
  | TSqr Term
  deriving (Show, Ord, Eq)

vars :: Term -> [VarId]
vars (TConst _) = []
vars (TVar v) = [v]
vars (TSqr a) = (vars a) 
vars (TAdd a b) = (vars a) ++ (vars b)
vars (TSub a b) = (vars a) ++ (vars b)
vars (TMul a b) = (vars a) ++ (vars b)

(.+.) = TAdd
(.-.) = TSub
(.*.) = TMul

con = TConst
var = TVar

(.==.) a b = (CEqz (TSub a b))
(.<.) a b = (CLez (TSub a b))
(.>.) a b = b .<. a

data Constraint = 
    CLez Term
  | CEqz Term
  deriving (Show, Ord, Eq) -- TODO: order by priority

data IConstraint = 
    ICLez Interval ITerm 
  | ICEqz Interval ITerm
  deriving (Show)

data ITerm = 
    ITConst Interval
  | ITVar Interval VarId
  | ITSqr Interval ITerm
  | ITAdd Interval ITerm ITerm
  | ITSub Interval ITerm ITerm
  | ITMul Interval ITerm ITerm
  deriving (Show)

cvars :: Constraint -> [VarId]
cvars (CLez a) = vars a
cvars (CEqz a) = vars a

hullConsistency :: [Constraint] -> IO Box
hullConsistency cs = hc4 cmap cs whole
  where whole = Map.fromList [ (v,I.whole) | v <- nub (join (map cvars cs)) ]
        cmap = Map.fromListWith (\a b -> nub $ a ++ b) [ (v,[c]) | c <- cs, length (cvars c) > 1, v <- cvars c ]

-- TODO prioritize constraints, e.g. take constraints with only one variable first
-- 
-- Worklist algorithm for fixpoint
hc4 :: Map.Map VarId [Constraint] -> [Constraint] -> Box -> IO Box
hc4 allC cs = go (Set.fromList cs)
  where
    go :: Set.Set Constraint -> Box -> IO Box
    go items box
      | Set.null items = return box
      | otherwise = do
          putStrLn $ "goiing" ++ (show item)
          if newBox /= box then do
            -- putStrLn $ "  changes:  " 
            -- putStrLn $ "    from: " ++ (show box)
            -- putStrLn $ "    to:   " ++ (show newBox)
            -- putStrLn $ "    diff: " ++ (show $ changedVars box newBox)
            -- putStrLn $ "  propagates to: " ++ (show propagate)
            go (Set.union propagate rest) newBox
          else go rest box
          where
            (item,rest) = (Set.elemAt 0 items, Set.deleteAt 0 items)
            newBox = hc4revise item box
            propagate :: Set.Set Constraint
            propagate = Set.fromList $ join $ catMaybes $ map (\v -> Map.lookup v allC) (changedVars box newBox)

changedVars :: Box -> Box -> [VarId]
changedVars a b = Map.keys $ Map.filter id $ 
  Map.intersectionWith (\ea eb -> ea /= eb) a b

negative = I.idouble $ fromJust $ I.interval (-(read "Infinity")) 0
positive = I.idouble $ fromJust $ I.interval 0 (read "Infinity")

initIntervalTree :: Box -> Constraint -> IConstraint
initIntervalTree b = sc
  where 
    sc (CLez t) = ICLez negative (st t)
    sc (CEqz t) = ICEqz (I.singleton 0) (st t)
    st (TConst c) = ITConst (I.singleton c)
    st (TVar v) = ITVar ((Map.!) b v) v
    st (TSqr a) = ITSqr I.whole (st a)
    st (TAdd a b) = ITAdd I.whole (st a) (st b)
    st (TSub a b) = ITSub I.whole (st a) (st b)
    st (TMul a b) = ITMul I.whole (st a) (st b)

hc4revise :: Constraint -> Box -> Box
hc4revise c b = backwardProp b (forwardEval (initIntervalTree b c))

(.&) = I.intersection
itermI :: ITerm -> Interval
itermI (ITConst i) = i
itermI (ITVar i _) = i
itermI (ITSqr i _) = i
itermI (ITAdd i _ _) = i
itermI (ITSub i _ _) = i
itermI (ITMul i _ _) = i

forwardEval :: IConstraint -> IConstraint
forwardEval = sc
  where
    sc (ICLez i t) = ICLez (i .& (iv (st t))) (st t)
    sc (ICEqz i t) = ICEqz (i .& (iv (st t))) (st t)

    st :: ITerm -> ITerm
    st (ITAdd i a b) = comb (+) ITAdd a b
    st (ITSqr i a) = comb1 (^2) ITSqr a
    st (ITSub i a b) = comb (-) ITSub a b
    st (ITMul i a b) = comb (*) ITMul a b
    st t = t

    iv = itermI
    comb op cstr a b = cstr (op (iv ta) (iv tb)) ta tb
      where ta = st a
            tb = st b
    comb1 op cstr a = cstr (op (iv ta)) ta
      where ta = st a

backwardProp :: Box -> IConstraint -> Box
backwardProp b c = execState (sc c) b 
  
  where
    sc :: IConstraint -> State Box ()
    sc (ICLez i t) = update i t
    sc (ICEqz i t) = update i t
    iv = itermI

    update :: Interval -> ITerm -> State Box ()
    update ri = st
      where
        st :: ITerm -> State Box ()
        st (ITVar i v) = modify (Map.adjust (\bi -> bi .& i .& ri) v)
        st (ITConst i) = if ri .& i == I.empty then error ("inconsistent  " ++ (show ri) ++ "--" ++ (show i)) else return () -- TODO: if empty, report inconsistency
        st (ITAdd i a b) = do update ((i .& ri) - (iv b)) a
                              update ((i .& ri) - (iv a)) b
        st (ITSub i a b) = do update ((i .& ri) + (iv b)) a
                              update ((iv a) - (i .& ri)) b
        st (ITMul i a b) = do update ((i .& ri) `myIntervalDiv` (iv b)) a
                              update ((i .& ri) `myIntervalDiv` (iv a)) b
        st (ITSqr i a) = update (sqrt (i .& ri)) a -- NOTE. this is only correct when a is always positive (sqrt is positive square root)

-- Inverse multiplication of intervals.
-- The division operator in the intervals package does not give
-- what we need here, so implemented explicitly.
--
infty = (read "Infinity") :: Double
myIntervalDiv :: Interval -> Interval -> Interval
myIntervalDiv ia ib
  | not (0 .@ ib)                  = ia/ib -- library OK for this case
  | a1 == 0 && a1 < a2 && b1 == 0 && b1 < b2 = 0 ... infty
  | 0 .@ ia && 0 .@ ib                       = I.whole
  | not (0 .@ ia) && ib == (I.singleton 0)   = I.empty
  | a2 < 0 && b1 < b2 && b2 == 0             = (a2/b1) ... infty
  | a2 < 0 && b1 < 0 && 0 < b2               = I.whole -- error "disjunct"
  | a2 < 0 && b1 == 0 && b1 < b2             = -infty ... (a2/b2)
  | a1 > 0 && b1 < b2 && b2 == 0             = -infty ... (a1/b1)
  | a1 > 0 && b1 < 0 && 0 < b2               = I.whole -- error "disjunct"
  | a1 > 0 && 0 == b1 && b1 < b2             = (a1/b2) ... infty
  where
    (a1,a2,b1,b2) = (I.inf ia, I.sup ia, I.inf ib, I.sup ib)
    (.@) = I.member

-- TODO: also interval multiplication with infinity is behaving strange
--   [0,infty]*[0,infty] = [infty,infty] ???  because 0*infty = NaN ?
-- myIntervalMul :: Interval -> Interval -> Interval
-- myIntervalMul ia ib = m a b c d
--   where
--     (a1,a2,b1,b2) = (I.inf ia, I.sup ia, I.inf ib, I.sup ib)
--     m 

(...) :: Double -> Double -> Interval
(...) a b = case (I.interval a b) of
  Just i -> i
  Nothing -> I.empty
