module SAT.FloatTheory.Constraints (
  FConstraint(..),
  FExpr(..),
  Model, 
  testModel,
  vars, cvars, 
  (.+.), (.-.), (.*.), (.==.), (.<=.), (.>=.)
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map (Map)

data FConstraint v = 
    CLez (FExpr v)
  | CEqz (FExpr v)
  deriving (Show, Ord, Eq) -- TODO: order by priority

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
  deriving (Show, Ord, Eq)

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

(.==.) a b = (CEqz (TSub a b))
(.<=.) a b = (CLez (TSub a b))
(.>=.) a b = b .<=. a

type Model varid = Map varid Double

testModel :: Ord v => [FConstraint v] -> Model v -> Bool
testModel cs m = foldl (&&) True (map (testConstraint (1e-5) m) cs)

testConstraint :: Ord v => Double -> Model v -> FConstraint v -> Bool
testConstraint tol m = evalC
  where

    evalC (CEqz t) = abs (evalT t) < tol
    evalC (CLez t) = evalT t - tol < 0.0

    evalT (TConst c) = c
    evalT (TVar v) = (Map.!) m v
    evalT (TAdd a b) = (+) (evalT a) (evalT b)
    evalT (TSub a b) = (-) (evalT a) (evalT b)
    evalT (TMul a b) = (*) (evalT a) (evalT b)
    evalT (TSqr a) = (^2) (evalT a)

