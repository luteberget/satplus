-- constraints on floating point numbers 

module SAT.FloatTheory (
   FloatSolver
  , newFloatSolver
  , solveWithFloat
  , floatConst
  , newFloat
  , (.+.) , (.-.) , (.*.)
  , (.==.) , (.<=.), (.>=.)
  , assertFloat
  )
 where

import qualified SAT 
-- import SAT.Bool
-- import SAT.Equal
-- import SAT.Order

import Data.IORef
import Data.Maybe (catMaybes)
import Control.Monad (forM, forM_)

import SAT.FloatTheory.Constraints

type VarId = Int
data FloatSolver = FloatSolver {
  solverPtr :: SAT.Solver,
  varCounter :: IORef VarId,
  constraints :: IORef [(SAT.Lit, FConstraint VarId)],
  fmodel :: IORef (Maybe (FModel VarId))
}

newFloatSolver :: SAT.Solver -> IO FloatSolver
newFloatSolver s = do
  counter <- newIORef 0
  constr <- newIORef []
  m <- newIORef Nothing
  return (FloatSolver s counter constr m)

floatConst :: Double -> FExpr VarId
floatConst x = TConst x

newFloat :: FloatSolver -> Double -> Double -> IO (FExpr VarId)
newFloat fs low high = do
  v <- readIORef (varCounter fs)
  modifyIORef (varCounter fs) (+1)
  let r = (TVar v)
  x1 <- assertFloat fs (r .>=. (floatConst low))
  x2 <- assertFloat fs (r .<=. (floatConst high))
  SAT.addClause (solverPtr fs) [x1] -- TODO keep unconditional constraints away from sat solver?
  SAT.addClause (solverPtr fs) [x2]
  return r

assertFloat :: FloatSolver -> FConstraint VarId -> IO SAT.Lit
assertFloat fs c = do
  l <- SAT.newLit (solverPtr fs)
  modifyIORef (constraints fs) ((l,c):)
  return l

solveConstraints :: [(SAT.Lit, FConstraint VarId)] -> IO (Either (FModel VarId) [SAT.Lit]) -- SAT model or UNSAT core
solveConstraints cs = do
  -- putStrLn ("Solving contraints" ++ (show cs))
  forM_ cs $ \c -> putStrLn (show c)
  --let (intervals,cs) = takeSimpleIntervalConstraints cs 
  return (Right [])

--takeSimpleIntervalConstraints :: 

solveWithFloat :: FloatSolver -> IO Bool
solveWithFloat fs = do
  boolsat <- SAT.solve (solverPtr fs) []
  if boolsat then do
    cs <- readIORef (constraints fs)
    cs <- fmap catMaybes $ forM cs $ \(lit,c) -> do
      active <- SAT.modelValue (solverPtr fs) lit
      if active then return (Just (lit,c)) else return Nothing
    r <- (solveConstraints cs)
    caseMatch r
  else do
    return False
 where 
   caseMatch :: Either (FModel VarId) [SAT.Lit] -> IO Bool
   caseMatch (Left model) = do
     writeIORef (fmodel fs) (Just model)
     return True
   caseMatch (Right []) = error "UNSAT with empty core"
   caseMatch (Right core) = do
     SAT.addClause (solverPtr fs) (map SAT.neg core)
     solveWithFloat fs
  
