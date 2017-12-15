module SAT.FloatTheory.Solver (
  solveMinimizeFloat
  ) where

-- Numerical floating point constraints solver.
--
-- Based on the HC4 hull consistency algorithm and the NLOpt library for local
-- search.
--
-- This solver gives answers fulfilling constraints within given tolerances, 
-- and makes no attempt to safely overapproximate floating point operations.
-- It is therefore not suitable for verification of floating point programs,
-- but is instead aimed at numerical engineering problems.
--

import Data.Maybe (isNothing)
import Control.Monad (filterM)
import Control.Monad.Identity
import Data.IORef
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe (fromJust, isNothing, isJust)

import qualified SAT
import SAT.FloatTheory.Constraints
import SAT.FloatTheory.Model
import SAT.FloatTheory.HullConsistency
import SAT.FloatTheory.Optimization
import SAT.FloatTheory.SolverObject

data TheoryStepResult  = TheorySat FloatModel 
                       | TheoryUnsatSubset [SAT.Lit] 

solveMinimizeFloat :: FloatSolver -> FloatExpr -> IO Bool
solveMinimizeFloat fs goal = do
  numVars <- readIORef (varCounter fs)
  cs <- readIORef (constraints fs)
  bgcs <- readIORef (backgroundConstraints fs)
  fparams <- readIORef (solverParams fs)
  go numVars cs bgcs fparams
  where 
    go numVars cs bgcs fparams = theoryLoop
      where
        theoryLoop :: IO Bool
        theoryLoop = do
          boolsat <- SAT.solve (solverPtr fs) []
          if boolsat then do
            activeC <- filterM (\(l,_) -> SAT.modelValue (solverPtr fs) l) cs
            step <- theoryStep activeC
            case step of
              TheorySat model -> do 
                writeIORef (fmodel fs) (Just model)
                return True
              TheoryUnsatSubset lits -> do 
                SAT.addClause (solverPtr fs) (map SAT.neg lits)
                theoryLoop
          else return False
          
        theoryStep :: [(SAT.Lit, FloatConstraint)] -> IO TheoryStepResult
        theoryStep activeC = do
          let hcResult = hc (bgcs ++ (map snd activeC))
          case hcResult of
            Nothing -> do
              let m = hcUnsatMinimal bgcs activeC
              return $ TheoryUnsatSubset m
            Just box -> do
              optModel <- optSolverModel box (map snd activeC)
              if testModel (map snd activeC) optModel then
                return (TheorySat optModel)
              else do
                m <- optUnsatMinimal box bgcs activeC
                return (TheoryUnsatSubset m)

        hc :: [FloatConstraint] -> Maybe Box
        hc = hullConsistency numVars (hcRelTol fparams) (hcIter fparams)

        hcUnsatMinimal :: [FloatConstraint] -> [(SAT.Lit, FloatConstraint)] 
                          -> [SAT.Lit]
        hcUnsatMinimal bg cs = map (fromJust.fst) (Set.toList min)
          where
            min = blackboxUnsatMinimal sat splitSet Set.union
                    (Set.fromList [(Nothing,c) | c <- bg]) 
                    (Set.fromList [(Just v, c) | (v,c) <- cs])
            sat s = isJust (hc (map snd (Set.toList s)))

        optSolverModel :: Box -> [FloatConstraint] -> IO FloatModel
        optSolverModel b c = nloptSat b goal c

        optUnsatMinimal :: Box -> [FloatConstraint] 
                           -> [(SAT.Lit,FloatConstraint)] -> IO [SAT.Lit]
        optUnsatMinimal box bg cs = undefined --map fst (Set.toList min)
          where
            min = blackboxUnsatMinimalM sat splitSet Set.union
                    (Set.fromList [(Nothing,c) | c <- bg]) 
                    (Set.fromList [(Just v, c) | (v,c) <- cs])
            sat s = fmap (testModel (map snd (Set.toList s)))
                         (optSolverModel box (map snd (Set.toList s)))

splitSet :: Set a -> (Set a, Maybe (Set a))
splitSet x = (a, if null b then Nothing else (Just b))
  where (m,half) = (Set.toAscList x, (Set.size x) `quot` 2)
        (a,b)    = (Set.fromDistinctAscList (take half m),
                    Set.fromDistinctAscList (drop half m))

blackboxUnsatMinimal sat sp jn ba st = runIdentity $
  (blackboxUnsatMinimalM (\x -> return $ sat x)) sp jn ba st

blackboxUnsatMinimalM :: Monad m => (p -> m Bool)  -- Satisifiable
                      -> (p -> (p,Maybe p))        -- Split 
                      -> (p -> p -> p)             -- Join
                      -> p -> p -> m p             -- Uncond. base + Cond. set
blackboxUnsatMinimalM sat split join = caseSplit 
  where 
    --caseSplit :: p -> p -> m p
    caseSplit base set = do
      let (a,b) = split set
      if isNothing b then return set
      else do
        satA <- sat (join base a)
        if not satA then caseSplit base a
        else do
          satB <- sat (join base (fromJust b))
          if not satB then caseSplit base (fromJust b)
          else do 
            caseA <- caseSplit (join base (fromJust b)) a
            caseB <- caseSplit (join base a) (fromJust b)
            return (join caseA caseB)
