-- constraints on floating point numbers 

module SAT.FloatTheory (
   FloatSolver
  , FloatExpr 
  , newFloatSolver
  , solveWithFloat
  , floatConst
  , newFloat
  , evalFloatExpr
  , (.+.) , (.-.) , (.*.)
  , (.==.) , (.<=.), (.>=.), square
  , mkFloatConstraint
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
import SAT.FloatTheory.Solver

type VarId = Int
type FloatExpr = FExpr VarId

data FloatSolver = FloatSolver {
  solverPtr :: SAT.Solver,
  varCounter :: IORef VarId,
  constraints :: IORef [(SAT.Lit, FConstraint VarId)],
  backgroundConstraints  :: IORef [FConstraint VarId],
  fmodel :: IORef (Maybe (FModel VarId))
}

newFloatSolver :: SAT.Solver -> IO FloatSolver
newFloatSolver s = do
  counter <- newIORef 0
  constr <- newIORef []
  bgConstr <- newIORef []
  m <- newIORef Nothing
  return (FloatSolver s counter constr bgConstr m)

floatConst :: Double -> FExpr VarId
floatConst x = TConst x

newFloat :: FloatSolver -> Double -> Double -> IO (FExpr VarId)
newFloat fs low high = do
  v <- readIORef (varCounter fs)
  modifyIORef (varCounter fs) (+1)
  let r = (TVar v)
  modifyIORef (backgroundConstraints fs) ((r .>=. (floatConst low)):)
  modifyIORef (backgroundConstraints fs) ((r .<=. (floatConst high)):)
  return r

mkFloatConstraint :: FloatSolver -> FConstraint VarId -> IO SAT.Lit
mkFloatConstraint fs c = do
  l <- SAT.newLit (solverPtr fs)
  modifyIORef (constraints fs) ((l,c):)
  return l

solveWithFloat :: FloatSolver -> IO Bool
solveWithFloat fs = do
  boolsat <- SAT.solve (solverPtr fs) []
  if boolsat then do
    cs <- readIORef (constraints fs)
    cs <- fmap catMaybes $ forM cs $ \(lit,c) -> do
      active <- SAT.modelValue (solverPtr fs) lit
      if active then return (Just (lit,c)) else return Nothing
    bgcs <- readIORef (backgroundConstraints fs)
    r <- (floatConjSat bgcs cs)
    case r of
      Sat model -> do
        putStrLn $ "floatsolv iteration SAT: " ++ (show model)
        writeIORef (fmodel fs) (Just model)
        return True
      Unsat core -> do
        putStrLn $ "floatsolv iteration UNSAT: " ++ (show core)
        SAT.addClause (solverPtr fs) (map SAT.neg core)
        solveWithFloat fs
      Unknown -> error "Float SAT unknown"
  else do
    putStrLn "SAT solver UNSAT"
    return False

evalFloatExpr :: FloatSolver -> FloatExpr -> IO Double
evalFloatExpr fs expr = do
  model <- readIORef (fmodel fs)
  case model of
    Just model -> return $ evalFExpr model expr
    Nothing -> error "Eval float expr called with no model."

