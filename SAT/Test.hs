{-# LANGUAGE TemplateHaskell #-}
module SAT.Test where

import SAT
import SAT.Bool
import qualified SAT.Unary as U
import SAT.Optimize

import Test.QuickCheck
import Test.QuickCheck.Modifiers
import Test.QuickCheck.Monadic
import Test.QuickCheck.All

------------------------------------------------------------------------------

prop_andl xs =
  satfun $ \s lit bol ->
    do y <- run $ andl s (map lit xs)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s y
       assert (a == and (map bol xs))

prop_orl xs =
  satfun $ \s lit bol ->
    do y <- run $ orl s (map lit xs)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s y
       assert (a == or (map bol xs))

prop_xorl xs =
  satfun $ \s lit bol ->
    do y <- run $ xorl s (map lit xs)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s y
       monitor (whenFail (putStrLn ("xorl " ++ show (map bol xs) ++ " = " ++ show a)))
       assert (a == odd (length (filter id (map bol xs))))

prop_implies x y =
  satfun $ \s lit bol ->
    do z <- run $ implies s (lit x) (lit y)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s z
       assert (a == (bol x <= bol y))

prop_equiv x y =
  satfun $ \s lit bol ->
    do z <- run $ equiv s (lit x) (lit y)
       b <- run $ solve s []
       assert b
       a <- run $ modelValue s z
       assert (a == (bol x == bol y))

------------------------------------------------------------------------------

prop_atMostOneOr pre xs =
  satfun $ \s lit bol ->
    do run $ atMostOneOr s (map lit pre) (map lit xs)
       b <- run $ solve s []
       monitor (whenFail (putStrLn ("atMostOneOr " ++ show (map bol pre) ++ " " ++ show (map bol xs) ++ " -> " ++ show b)))
       assert (or (map bol pre) || b == (length (filter id (map bol xs)) <= 1))

prop_parityOr pre xs p =
  satfun $ \s lit bol ->
    do run $ parityOr s (map lit pre) (map lit xs) p
       b <- run $ solve s []
       monitor (whenFail (putStrLn ("parityOr " ++ show (map bol pre) ++ " " ++ show (map bol xs) ++ " " ++ show p ++ " -> " ++ show b)))
       assert (or (map bol pre) || b == (p == odd (length (filter id (map bol xs)))))

------------------------------------------------------------------------------

prop_unaryLeq (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..<= k)
       assert (a == (n <= k))

prop_unaryLt (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..< k)
       assert (a == (n < k))

prop_unaryGeq (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..>= k)
       assert (a == (n >= k))

prop_unaryGt (NonNegative m) (NonNegative k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       b <- run $ solve s []
       assert b
       n <- run $ U.modelValue s u
       a <- run $ modelValue s (u U..> k)
       assert (a == (n > k))

prop_unary_add (NonNegative m1) (NonNegative m2) =
  satfun $ \s lit bol ->
    do u1 <- run $ U.newUnary s m1
       u2 <- run $ U.newUnary s m2
       k1 <- pick (choose (0,m1))
       k2 <- pick (choose (0,m2))
       u3 <- run $ U.add s u1 u2
       b <- run $ solve s [u1 U..>= k1, u2 U..>= k2]
       assert b
       n1 <- run $ U.modelValue s u1
       n2 <- run $ U.modelValue s u2
       n3 <- run $ U.modelValue s u3
       assert (n3 == n1+n2)

prop_unary_count xs =
  satfun $ \s lit bol ->
    do u <- run $ U.count s (map lit xs)
       b <- run $ solve s []
       assert b
       n  <- run $ U.modelValue s u
       bs <- run $ sequence [ modelValue s (lit x) | x <- xs ]
       assert (length (filter id bs) == n)

prop_unary_div (NonNegative m) (Positive k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       b <- run $ solve s [u U..>= i]
       assert b
       n  <- run $ U.modelValue s u
       nk <- run $ U.modelValue s (u U.// k)
       assert (nk == (n `div` k))

prop_unary_mod (NonNegative m) (Positive k) =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       uk <- run $ U.modulo s u k
       b <- run $ solve s [u U..>= i]
       assert b
       n  <- run $ U.modelValue s u
       nk <- run $ U.modelValue s uk
       assert (nk == (n `mod` k))

------------------------------------------------------------------------------

prop_minimize (NonNegative m) as =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       run $ addClause s [u U..>= i]
       b <- run $ solveMinimize s (map lit as) u
       assert (b == (False `notElem` map bol as))
       if b then
         do n <- run $ U.modelValue s u
            monitor (whenFail $ putStrLn ("n=" ++ show n ++ ", i=" ++ show i))
            assert (n == i)
        else
         do monitor (whenFail $ putStrLn ("b=" ++ show b ++ ", as=" ++ show (map bol as)))

prop_maximize (NonNegative m) as =
  satfun $ \s lit bol ->
    do u <- run $ U.newUnary s m
       i <- pick (choose (0,m))
       run $ addClause s [u U..<= i]
       b <- run $ solveMaximize s (map lit as) u
       assert (b == (False `notElem` map bol as))
       if b then
         do n <- run $ U.modelValue s u
            monitor (whenFail $ putStrLn ("n=" ++ show n ++ ", i=" ++ show i))
            assert (n == i)
        else
         do monitor (whenFail $ putStrLn ("b=" ++ show b ++ ", as=" ++ show (map bol as)))

------------------------------------------------------------------------------

testAll = $(quickCheckAll)

------------------------------------------------------------------------------

satfun h =
  monadicIO $
    do s  <- run $ newSolver
       ps <- run $ sequence [ newLit s | i <- [1..100] ]
       Blind bs <- pick $ Blind `fmap` sequence [ arbitrary | p <- ps ]
       run $ sequence_ [ addClause s [ if b then p else neg p ]
                       | (p,b) <- ps `zip` bs
                       ]

       let lit (LIT x) = if x > 0 then p else neg p
            where
             p = (true : ps) !! (abs x - 1)

           bol (LIT x) = if x > 0 then p else not p
            where
             p = (True : bs) !! (abs x - 1)

       h s lit bol

data LIT = LIT Int
 deriving ( Eq, Ord )

instance Show LIT where
  show (LIT 1)    = "TRUE"
  show (LIT (-1)) = "FALSE"
  show (LIT x)    = show x

instance Arbitrary LIT where
  arbitrary =
    LIT `fmap`
      sized (\s -> let n = 1+(s`div` 8) in
              choose (-n, n) `suchThat` (/=0))

  shrink (LIT x) =
    [ LIT (-1) | x /= (-1) ] ++
    [ LIT 1    | abs x /= 1 ]
