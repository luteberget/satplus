module SAT.FloatTheory.HullConsistency (
  hullConsistency,
  Box
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (catMaybes)
import Control.Monad.State

import SAT.FloatTheory.Interval (Interval, interval)
import qualified SAT.FloatTheory.Interval as I
import SAT.FloatTheory.Constraints

type Box v = Map.Map v Interval

data IConstraint var =
    ICLez Interval (ITerm var)
  | ICEqz Interval (ITerm var)
  deriving (Show)

data ITerm var =
    ITConst Interval
  | ITVar Interval var
  | ITSqr Interval (ITerm var)
  | ITAdd Interval (ITerm var) (ITerm var)
  | ITSub Interval (ITerm var) (ITerm var)
  | ITMul Interval (ITerm var) (ITerm var)
  deriving (Show)

nub :: Ord a => [a] -> [a]
nub = Set.toList . Set.fromList

hullConsistency :: (Ord var, Show var) => [FConstraint var] -> IO (Maybe (Box var))
hullConsistency cs = hc4 cmap cs whole
  where whole = Map.fromList [ (v,I.whole) | v <- nub (join (map cvars cs)) ]
        cmap = Map.fromListWith (\a b -> nub $ a ++ b) [ (v,[c]) | c <- cs, length (cvars c) > 1, v <- cvars c ]
-- note that constraints having (length cvars = 1) have no use 
-- of having new information propagated into them.

-- TODO prioritize constraints, e.g. take constraints with only one variable first
-- 
-- Worklist algorithm for fixpoint
hc4 :: (Ord var, Show var) => Map.Map var [FConstraint var] -> [FConstraint var] -> Box var -> IO (Maybe (Box var))
hc4 allC cs = go (Set.fromList cs)
  where
    --go :: Set.Set (FConstraint var) -> Box v -> IO (Maybe (Box var))
    go items box
      | Set.null items = return $ Just box
      | otherwise = do
          -- putStrLn $ "*-> " ++ (show item)
          case newBox of
            Just newBox -> if newBox /= box then do
                let propagate = Set.fromList $ join $ catMaybes $ map (\v -> Map.lookup v allC) (changedVars box newBox)
                -- putStrLn $ "  changes:  "
                -- putStrLn $ "    from: " ++ (show box)
                -- putStrLn $ "    to:   " ++ (show newBox)
                -- putStrLn $ "    diff: " ++ (show $ changedVars box newBox)
                -- putStrLn $ "  propagates to: " ++ (show propagate)
                go (Set.union propagate rest) newBox
              else go rest box
            Nothing -> return Nothing
          where
            (item,rest) = (Set.elemAt 0 items, Set.deleteAt 0 items)
            newBox = hc4revise item box

changedVars :: Ord v => Box v -> Box v -> [v]
changedVars a b = Map.keys $ Map.filter id $
  Map.intersectionWith (\ea eb -> ea /= eb) a b

initIntervalTree :: Ord v => Box v -> FConstraint v -> IConstraint v
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

hc4revise :: Ord v => FConstraint v -> Box v -> Maybe (Box v)
hc4revise c b = backwardProp b (forwardEval (initIntervalTree b c))

(.&) = I.intersection
itermI :: ITerm v -> Interval
itermI (ITConst i) = i
itermI (ITVar i _) = i
itermI (ITSqr i _) = i
itermI (ITAdd i _ _) = i
itermI (ITSub i _ _) = i
itermI (ITMul i _ _) = i


forwardEval :: IConstraint v -> IConstraint v
forwardEval = sc
  where
    sc (ICLez i t) = ICLez (i .& (iv (st t))) (st t)
    sc (ICEqz i t) = ICEqz (i .& (iv (st t))) (st t)

    --st :: ITerm v -> ITerm v
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



backwardProp :: Ord v => Box v -> IConstraint v -> Maybe (Box v)
backwardProp b c = execState (sc c) (Just b)

  where
    --sc :: IConstraint v -> State (Maybe (Box v)) ()
    sc (ICLez i t) = update i t
    sc (ICEqz i t) = update i t
    iv = itermI

    update :: Ord v => Interval -> ITerm v -> State (Maybe (Box v)) ()
    update ri = st
      where
        -- st :: ITerm -> State (Maybe (Box v)) ()
        st (ITVar i v)
          | ri .& i == I.empty = put Nothing -- Fail
          | otherwise = modify (fmap (Map.adjust (\bi -> bi .& i .& ri) v))
        st (ITConst i)
          | ri .& i == I.empty = put Nothing -- Fail
          | otherwise = return ()

        st (ITAdd i a b) = do update ((i .& ri) `I.sub` (iv b)) a
                              update ((i .& ri) `I.sub` (iv a)) b
        st (ITSub i a b) = do update ((i .& ri) `I.add` (iv b)) a
                              update ((iv a) `I.sub` (i .& ri)) b
        st (ITMul i a b) = do update ((i .& ri) `I.invmul` (iv b)) a
                              update ((i .& ri) `I.invmul` (iv a)) b
        st (ITSqr i a) = update (I.sqrt (i .& ri)) a -- NOTE. this is only correct when a is always positive (sqrt is positive square root)

