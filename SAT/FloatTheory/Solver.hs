module SAT.FloatTheory.Solver (
  ) where

-- Partial decision of satisfiability of conjunctions of 
-- floating point constraints, with a numerical tolerance.
--
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map (Map)

import SAT.FloatTheory.Constraints
import SAT.FloatTheory.HullConsistency
import SAT.FloatTheory.Interval (Interval, interval)
import qualified SAT.FloatTheory.Interval as I

data FloatSatResult v = Sat (FModel v) | Unsat [FConstraint v] | Unknown 
  deriving (Show)

floatingConjSat :: (Show v, Ord v) => [FConstraint v] -> IO (FloatSatResult v)
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

-- TODO get rid of this 
splitMid :: [a] -> ([a],[a])
splitMid l = splitAt (((length l) + 1) `div` 2) l

sample :: (Show v, Ord v) => Box v -> IO (FModel v)
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


resultBox :: (Show v, Ord v) => [FConstraint v] -> Box v -> IO (FloatSatResult v)
resultBox cs box = do
  model <- sample box
  let test = testModel cs model
  let g
        | test      = return $ Sat model
        | otherwise = return $ Unknown
  g

