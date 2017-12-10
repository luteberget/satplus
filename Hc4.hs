module Hc4 where

-- Partial decision of satisfiability of conjunctions of 
-- floating point constraints, with a numerical tolerance.

-- import qualified Numeric.Interval as I
import Control.Monad (join)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.State

import SAT.FloatTheory.Interval (Interval, interval)
import qualified SAT.FloatTheory.Interval as I

-- TODO: nub is bad, try something like nub = toList . Set.fromList ? 

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

hullConsistency :: [Constraint] -> IO (Maybe Box)
hullConsistency cs = hc4 cmap cs whole
  where whole = Map.fromList [ (v,I.whole) | v <- nub (join (map cvars cs)) ]
        cmap = Map.fromListWith (\a b -> nub $ a ++ b) [ (v,[c]) | c <- cs, length (cvars c) > 1, v <- cvars c ]
-- note that constraints having (length cvars = 1) have no use 
-- of having new information propagated into them.

-- TODO prioritize constraints, e.g. take constraints with only one variable first
-- 
-- Worklist algorithm for fixpoint
hc4 :: Map.Map VarId [Constraint] -> [Constraint] -> Box -> IO (Maybe Box)
hc4 allC cs = go (Set.fromList cs)
  where
    go :: Set.Set Constraint -> Box -> IO (Maybe Box)
    go items box
      | Set.null items = return $ Just box
      | otherwise = do
          putStrLn $ "*-> " ++ (show item)
          case newBox of
            Just newBox -> if newBox /= box then do
                let propagate = Set.fromList $ join $ catMaybes $ map (\v -> Map.lookup v allC) (changedVars box newBox)
                putStrLn $ "  changes:  " 
                putStrLn $ "    from: " ++ (show box)
                putStrLn $ "    to:   " ++ (show newBox)
                putStrLn $ "    diff: " ++ (show $ changedVars box newBox)
                putStrLn $ "  propagates to: " ++ (show propagate)
                go (Set.union propagate rest) newBox
              else go rest box
            Nothing -> return Nothing
          where
            (item,rest) = (Set.elemAt 0 items, Set.deleteAt 0 items)
            newBox = hc4revise item box

-- Some stuff from thinking about implementing CDCL
--
--data Complementable =
--    VarGe Double
--  | VarLt Double
--
--complement :: Complementable -> Complementable
--complement (VarGe x) = VarLt x
--complement (VarLt x) = VarGe x
--
--decompose :: Interval -> [Complementable]
--decompose i = filter f [VarGe a, VarLt b]
--  where 
--    (a,b) = (I.lowerBound i, I.upperBound i)
--    f (VarGe x) = not (isInfinite x)
--    f (VarLt x) = not (isInfinite x)

  

changedVars :: Box -> Box -> [VarId]
changedVars a b = Map.keys $ Map.filter id $ 
  Map.intersectionWith (\ea eb -> ea /= eb) a b

initIntervalTree :: Box -> Constraint -> IConstraint
initIntervalTree b = sc
  where 
    sc (CLez t) = ICLez I.negative (st t)
    sc (CEqz t) = ICEqz (I.singleton 0) (st t)
    st (TConst c) = ITConst (I.singleton c)
    st (TVar v) = ITVar ((Map.!) b v) v
    st (TSqr a) = ITSqr I.whole (st a)
    st (TAdd a b) = ITAdd I.whole (st a) (st b)
    st (TSub a b) = ITSub I.whole (st a) (st b)
    st (TMul a b) = ITMul I.whole (st a) (st b)

hc4revise :: Constraint -> Box -> Maybe Box
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
    st (ITAdd i a b) = comb I.add ITAdd a b
    st (ITSqr i a) = comb1 ((flip I.pow) 2) ITSqr a
    st (ITSub i a b) = comb I.sub ITSub a b
    st (ITMul i a b) = comb I.mul ITMul a b
    st t = t

    iv = itermI
    comb op cstr a b = cstr (op (iv ta) (iv tb)) ta tb
      where ta = st a
            tb = st b
    comb1 op cstr a = cstr (op (iv ta)) ta
      where ta = st a

backwardProp :: Box -> IConstraint -> Maybe Box
backwardProp b c = execState (sc c) (Just b)
  
  where
    sc :: IConstraint -> State (Maybe Box) ()
    sc (ICLez i t) = update i t
    sc (ICEqz i t) = update i t
    iv = itermI

    mkFail :: State (Maybe Box) ()
    mkFail = put Nothing

    update :: Interval -> ITerm -> State (Maybe Box) ()
    update ri = st
      where
        st :: ITerm -> State (Maybe Box) ()
        st (ITVar i v)
          | ri .& i == I.empty = mkFail
          | otherwise = modify (fmap (Map.adjust (\bi -> bi .& i .& ri) v))
        st (ITConst i) 
          | ri .& i == I.empty = mkFail
          | otherwise = return ()

-- if ri .& i == I.empty then error ("inconsistent  " ++ (show ri) ++ "--" ++ (show i)) else return () -- TODO: if empty, report inconsistency
--
        st (ITAdd i a b) = do update ((i .& ri) `I.sub` (iv b)) a
                              update ((i .& ri) `I.sub` (iv a)) b
        st (ITSub i a b) = do update ((i .& ri) `I.add` (iv b)) a
                              update ((iv a) `I.sub` (i .& ri)) b
        st (ITMul i a b) = do update ((i .& ri) `I.invmul` (iv b)) a
                              update ((i .& ri) `I.invmul` (iv a)) b
        st (ITSqr i a) = update (I.sqrt (i .& ri)) a -- NOTE. this is only correct when a is always positive (sqrt is positive square root)

-- Inverse multiplication of intervals.
-- The division operator in the intervals package does not give
-- what we need here, so implemented explicitly.
--
infty = (read "Infinity") :: Double
-- myIntervalDiv :: Interval -> Interval -> Interval
-- myIntervalDiv ia ib
--   | not (0 .@ ib)                  = ia/ib -- library OK for this case
--   | a1 == 0 && a1 < a2 && b1 == 0 && b1 < b2 = 0 ... infty
--   | 0 .@ ia && 0 .@ ib                       = I.whole
--   | not (0 .@ ia) && ib == (I.singleton 0)   = I.empty
--   | a2 < 0 && b1 < b2 && b2 == 0             = (a2/b1) ... infty
--   | a2 < 0 && b1 < 0 && 0 < b2               = I.whole -- error "disjunct"
--   | a2 < 0 && b1 == 0 && b1 < b2             = (-infty) ... (a2/b2)
--   | a1 > 0 && b1 < b2 && b2 == 0             = (-infty) ... (a1/b1)
--   | a1 > 0 && b1 < 0 && 0 < b2               = I.whole -- error "disjunct"
--   | a1 > 0 && 0 == b1 && b1 < b2             = (a1/b2) ... infty
--   where
--     (a1,a2,b1,b2) = (I.lowerBound ia, I.upperBound ia, I.lowerBound ib, I.upperBound ib)
--     (.@) = I.member

-- TODO: also interval multiplication with infinity is behaving strange
--   [0,infty]*[0,infty] = [infty,infty] ???  because 0*infty = NaN ?
-- myIntervalMul :: Interval -> Interval -> Interval
-- myIntervalMul ia ib = m a b c d
--   where
--     (a1,a2,b1,b2) = (I.lowerBound ia, I.upperBound ia, I.lowerBound ib, I.upperBound ib)
--     m 

(...) :: Double -> Double -> Interval
(...) = I.interval

-- model search
-- incomplete procedure, assumes no splitting is needed, i.e. that only interval propagation is enough.
-- If SAT, then HC4 will produce the model. (If not, we return unknown)
-- If UNSAT, we have two main choices:
--   * Black box binary search on constraint set.
--     Minimize procedure: Split set of constraints in two: A and B. 
--       1. If one of them is UNSAT, continue with it (if both are, pick any).
--       2. If both are SAT, minimize each under the assumption of the other.
--   * When deducing, maintain graph of each variable's intervals with constraints as edges to 
--     after-propagation variable intervals. When a constraint causes UNSAT, go back and collect
--     all involved constraints.
--


data FloatSatResult = Sat Model | Unsat UnsatCore | Unknown deriving (Show)

-- type Lit = Int
type UnsatCore = [Constraint] -- set of literals?
type Model = Map VarId Double
-- data Trail = Trail {
--     trailBox :: Box,
--     trailReasons :: [Constraint],
--     trailPrev :: Maybe Trail
--   }
-- 
-- addTrail :: Trail -> Box -> Trail
-- addTrail = undefined -- q <- ded(tr), tr <- tr * q

-- modelSearchStart :: [(Lit,Constraint)] -> Either UnsatCore Model
-- 
-- modelSearch :: Trail -> [(Int,Constraint)] -> IO (Either UnsatCore Model)
-- modelSearch tr cs  = do

sample :: Box -> IO Model 
sample m = do
  n <- sequence [do putStrLn $ "sampling " ++ (show v)
                    x <- sampleI v
                    putStrLn $ "  -> " ++ (show (not (isInfinite (I.lowerBound v))))
                    return (k,x)
                 | (k,v) <- Map.toList m ]
  return (Map.fromList n)
  where 
    sampleI :: Interval -> IO Double
    sampleI i
-- TODO: remove these cases now that we have finiteSample
      | not (isNaN (I.finiteSample i)) && not (isInfinite (I.finiteSample i)) = return $ I.finiteSample i
      | not (isInfinite (I.lowerBound i)) = return $ I.lowerBound i
      | not (isInfinite (I.upperBound i)) = return $ I.upperBound i
      | I.member 0.0 i = return 0.0
      | otherwise = error "could not sample interval"

testModel :: [Constraint] -> Model -> Bool
testModel cs m = foldl (&&) True (map (testConstraint (1e-5) m) cs)

testConstraint :: Double -> Model -> Constraint -> Bool
testConstraint tol m = evalC
  where
    evalC :: Constraint -> Bool
    evalC (CEqz t) = abs (evalT t) < tol
    evalC (CLez t) = evalT t - tol < 0.0
    evalT :: Term -> Double
    evalT (TConst c) = c
    evalT (TVar v) = (Map.!) m v
    evalT (TAdd a b) = (+) (evalT a) (evalT b)
    evalT (TSub a b) = (-) (evalT a) (evalT b)
    evalT (TMul a b) = (*) (evalT a) (evalT b)
    evalT (TSqr a) = (^2) (evalT a)

resultBox :: [Constraint] -> Box -> IO FloatSatResult
resultBox cs box = do 
  model <- sample box
  let test = testModel cs model
  let g
        | test      = return $ Sat model
        | otherwise = return $ Unknown
  g

-- floatingConjSat :: [Constraint] -> IO (Maybe Model)
-- floatingConjSat cs = do
--   box <- hullConsistency cs
--   case box of
--     Just b -> do
--       putStrLn $ "floatingConjSat: sat, testing model with " ++ (show $ sample b)
--       return (resultBox cs b)
--     Nothing -> do
--       putStrLn $ "floatingConjSat: unsat, finding core"
--       fmap Unsat $ (caseSplit [] cs)

floatingConjSat :: [Constraint] -> IO FloatSatResult
floatingConjSat cs = do
  box <- hullConsistency cs
  case box of
    Just b -> do
       putStrLn $ "floatingConjSat: sat, testing model"
       resultBox cs b
    Nothing -> do
       putStrLn $ "floatingConjSat: unsat, finding core"
       core <- blackboxUnsatCore hullConsistency splitMid cs
       return (Unsat core)

splitMid :: [a] -> ([a],[a])
splitMid l = splitAt (((length l) + 1) `div` 2) l


blackboxUnsatCore :: Show p => ([p] -> IO (Maybe m)) -> 
                     ([p] -> ([p],[p])) -> 
                     [p] -> IO [p]
blackboxUnsatCore satF split ps = caseSplit [] ps
  where
    -- Assumption: satF (base ++ ps) == Nothing
    -- caseSplit :: [p] -> [p] -> IO [p]
    caseSplit base ps = do
      putStrLn $ "ENTERED caseSplit with base=" ++ (show base) ++ ", ps=" ++ (show ps)
      let (a,b) = split ps
      putStrLn $ "split into " ++ (show (a,b))
      if length b == 0 then return (base ++ a)
      else do
        -- Try sat base + a
        satA <- satF (base ++ a)
        case satA of 
          Nothing -> caseSplit base a -- base + a is unsat
          Just modelA -> do  -- base + a is SAT with model
            -- Try sat base + b
            satB <- satF (base ++ b)
            case satB of
              Nothing -> caseSplit base b -- base + b is unsat
              Just modelB -> do
                -- Both a and b are SAT (under base), so minimize each under the other
                coreA <- caseSplit (base ++ b) a
                coreB <- caseSplit (base ++ a) b
                return (coreA ++ coreB)

-- caseSplit :: [Constraint] -> [Constraint] -> IO UnsatCore
-- caseSplit base cs = do
--   let (a,b) = ([]::[Constraint],[]::[Constraint])
--   satA <- floatingConjSat (base ++ a)
--   case satA of
--     Unknown -> error $ "floatingConjSat could not solve " ++ (show a)
--     Unsat x -> caseSplit [] a
--     Sat modelA -> do
--       satB <- floatingConjSat (base ++ b)
--       case satB of
--         Unknown -> error $ "floatingConjSat could not solve " ++ (show b)
--         Unsat x -> caseSplit [] b
--         Sat modelB -> do
--           coreA <- caseSplit b a
--           coreB <- caseSplit a b
--           return $ Set.union coreA coreB
