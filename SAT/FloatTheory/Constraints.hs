module SAT.FloatTheory.Constraints (
  FConstraint(..),
  FExpr(..),
  FModel, 
  testModel,
  evalFExpr,
  vars, cvars, 
  (.+.), (.-.), (.*.), (.==.), (.<=.), (.>=.), square
  ) where


-- TODO REMOVE constraint, replace with interval and fexpr

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map (Map)

data FConstraint v = 
    CLez (FExpr v)
  | CEqz (FExpr v)
  deriving (Ord, Eq) -- TODO: order by priority

instance Show v => Show (FConstraint v) where
  show (CLez e) = (show e) ++ " <= 0"
  show (CEqz e) = (show e) ++ " == 0"

cvars :: FConstraint v -> [v]
cvars (CLez a) = vars a
cvars (CEqz a) = vars a

data FExpr varid = 
    TConst Double
  | TVar varid
  | TAdd (FExpr varid) (FExpr varid)
  | TSub (FExpr varid) (FExpr varid)
  | TMul (FExpr varid) (FExpr varid)
  | TSqr (FExpr varid)
  deriving (Ord, Eq)

instance Show v => Show (FExpr v) where
  show (TConst d) = show d
  show (TVar v) = "x" ++ (show v)
  show (TAdd a b) = "(" ++ (show a) ++ " + " ++ (show b) ++ ")"
  show (TSub a b) = "(" ++ (show a) ++ " - " ++ (show b) ++ ")"
  show (TMul a b) = "(" ++ (show a) ++ " * " ++ (show b) ++ ")"
  show (TSqr a) = "(" ++ (show a) ++ "^2)"

vars :: FExpr varid -> [varid]
vars (TConst _) = []
vars (TVar v) = [v]
vars (TSqr a) = (vars a) 
vars (TAdd a b) = (vars a) ++ (vars b)
vars (TSub a b) = (vars a) ++ (vars b)
vars (TMul a b) = (vars a) ++ (vars b)

(.+.) = TAdd
(.-.) = TSub
(.*.) = TMul
square = TSqr

(.==.) a b = (CEqz (TSub a b))
(.<=.) a b = (CLez (TSub a b))
(.>=.) a b = b .<=. a

type FModel varid = Map varid Double

testModel :: Ord v => [FConstraint v] -> FModel v -> Bool
testModel cs m = foldl (&&) True (map (testConstraint (1e-5) m) cs)

testConstraint :: Ord v => Double -> FModel v -> FConstraint v -> Bool
testConstraint tol m (CEqz t) = abs (evalFExpr m t) < tol
testConstraint tol m (CLez t) = (evalFExpr m t) - tol < 0.0

evalFExpr :: Ord v => FModel v -> FExpr v -> Double
evalFExpr m = evalT
  where
    evalT (TConst c) = c
    evalT (TVar v) = (Map.!) m v
    evalT (TAdd a b) = (+) (evalT a) (evalT b)
    evalT (TSub a b) = (-) (evalT a) (evalT b)
    evalT (TMul a b) = (*) (evalT a) (evalT b)
    evalT (TSqr a) = (^2) (evalT a)

