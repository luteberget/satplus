module SAT.Order where

import SAT
import SAT.Equal
import SAT.Util

import Prelude hiding ( Ordering(..) )
import Control.Monad ( when )

------------------------------------------------------------------------------

data Compare = LT | LEQ | GEQ | GT
 deriving ( Eq, Ord, Show, Read )

class Order a where
  compareOr :: Solver -> [Lit] -> Compare -> a -> a -> IO ()
  compareOr s pre cmp x y = compareTupleOr s pre cmp (x,()) (y,())

  newCompareLit :: Solver -> Compare -> a -> a -> IO Lit
  newCompareLit s cmp x y =
    do q <- newLit s
       compareOr s [neg q] cmp x y
       return q

  compareTupleOr :: Order b => Solver -> [Lit] -> Compare -> (a,b) -> (a,b) -> IO ()

------------------------------------------------------------------------------

greaterThan, greaterThanEqual, lessThan, lessThanEqual ::
  Order a => Solver -> a -> a -> IO ()
greaterThan      = unconditionally greaterThanOr
greaterThanEqual = unconditionally greaterThanEqualOr
lessThan         = unconditionally lessThanOr
lessThanEqual    = unconditionally lessThanEqualOr

greaterThanOr, greaterThanEqualOr, lessThanOr, lessThanEqualOr ::
  Order a => Solver -> [Lit] -> a -> a -> IO ()
greaterThanOr      s pre x y = compareOr s pre GT  (x,()) (y,())
greaterThanEqualOr s pre x y = compareOr s pre GEQ (x,()) (y,())
lessThanOr         s pre x y = compareOr s pre LT  (x,()) (y,())
lessThanEqualOr    s pre x y = compareOr s pre LEQ (x,()) (y,())

isGreaterThan, isGreaterThanEqual, isLessThan, isLessThanEqual ::
  Order a => Solver -> a -> a -> IO Lit
isGreaterThan      s x y = isLessThan s y x
isGreaterThanEqual s x y = isLessThanEqual s y x
isLessThan         s x y = neg `fmap` isGreaterThanEqual s x y
isLessThanEqual    s x y =
  do q <- newCompareLit s LEQ x y
     compareOr s [q] GT x y
     return q

------------------------------------------------------------------------------

instance Order () where
  compareOr s pre cmp _ _
    | isFalse   = addClause s pre
    | otherwise = return ()
   where
    isFalse = cmp `elem` [LT,GT]

  newCompareLit s cmp _ _
    | cmp `elem` [LT,GT] = return false
    | otherwise          = return true

  compareTupleOr s pre cmp (_,p) (_,q) =
    compareOr s pre cmp p q

instance Order Bool where
  compareTupleOr s pre cmp (x,p) (y,q)
    | x == y    = compareOr s pre cmp p q
    | isFalse   = addClause s pre
    | otherwise = return ()
   where
    isFalse = (cmp,x) `elem` [(LT,True), (LEQ,True), (GT,False), (GEQ,False)]

  newCompareLit s cmp x y
    | x == y    = return (bool (cmp `elem` [LEQ,GEQ]))
    | isFalse   = return false
    | otherwise = return true
   where
    isFalse = (cmp,x) `elem` [(LT,True), (LEQ,True), (GT,False), (GEQ,False)]

instance Order Lit where
  compareTupleOr s pre cmp (x,p) (y,q)
    | x == y    = compareOr s pre cmp p q
    | otherwise =
      do w <- newCompareLit s cmp p q
         when (cmp `elem` [LT, LEQ]) $
           do addClause s [y, w]
              addClause s [neg x, w]
              addClause s [neg x, y]
         when (cmp `elem` [GT, GEQ]) $
           do addClause s [x, w]
              addClause s [neg y, w]
              addClause s [neg y, x]

instance (Order a, Order b) => Order (a,b) where
  compareOr s pre cmp t1 t2 =
    compareTupleOr s pre cmp t1 t2

  compareTupleOr s pre cmp t1 t2 =
    compareTupleOr s pre cmp (encTuple t1) (encTuple t2)

encTuple ((x,y),r) = (x,(y,r))

instance (Order a, Order b) => Order (Either a b) where
  compareTupleOr s pre cmp (Left x1,z1) (Left x2,z2) =
    compareTupleOr s pre cmp (x1,z1) (x2,z2)

  compareTupleOr s pre cmp (Right y1,z1) (Right y2,z2) =
    compareTupleOr s pre cmp (y1,z1) (y2,z2)

  compareTupleOr s pre cmp (Left _,z1) (Right _,z2) =
    compareOr s pre cmp False True

  compareTupleOr s pre cmp (Right _,z1) (Left _,z2) =
    compareOr s pre cmp True False

------------------------------------------------------------------------------

instance (Order a, Order b, Order c) => Order (a,b,c) where
  compareTupleOr s pre cmp t1 t2 =
    compareTupleOr s pre cmp (encTriple t1) (encTriple t2)

encTriple ((x,y,z),r) = (x,(y,(z,r)))

instance Order a => Order (Maybe a) where
  compareTupleOr s pre cmp m1 m2 =
    compareTupleOr s pre cmp (encMaybe m1) (encMaybe m2)

encMaybe (Nothing, r) = (Left (), r)
encMaybe (Just x,  r) = (Right x, r)

instance Order a => Order [a] where
  compareTupleOr s pre cmp l1 l2 =
    compareTupleOr s pre cmp (encList l1) (encList l2)

encList ([],     r) = (Left (),      r)
encList ((x:xs), r) = (Right (x,xs), r)
