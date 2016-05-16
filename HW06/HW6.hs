{-# LANGUAGE Rank2Types, ExistentialQuantification #-}
{-# OPTIONS -W #-}

module HW6 where

--Won Yong Ha
-- Brandon, Scott, Simon

--Start: Feb 20 2016
--End: Feb 22 2016

import Data.List

-- Welcome to Homework 6: Type abstraction.
-- Modify this Haskell code and upload it as a single .hs file.
-- We will grade it for correctness, clarity, and modularity.
-- We might show it in class as an example that everyone can learn from.
-- Late homework will receive half credit if submitted by the next lecture.

-- Reminders:
-- Start early.
-- Work together. List who you worked with. Submit only your own writing.
-- Ask questions during lecture, in online discussion, at office hours.
-- Avoid code duplication where possible by abstracting similar functions.
-- Make sure that your code typechecks by loading it in GHC.
-- Document your code by giving a brief description of each function,
-- and by giving each function a type signature.
-- Don't put junk in your type. Don't jam special cases into your type.

-- Section 1 (50%) -------------------------------------------------------------
-- Type classes vs dictionary passing

--  1. (5%) Write a function "count" that returns the number of times a given
--     value appears in a list.  For example:
--
--      count 3 [1,2,3,4,5,4,3,2,1] == 2
--      count 7 [1,2,3,4,5,4,3,2,1] == 0

count :: (Eq a) => a -> [a] -> Int
count _ []    = 0
count n (x:xs)
  | x == n    = 1 + count n xs
  | otherwise = count n xs

--  2. (5%) Write a function "merge" that combines two sorted lists into one.
--     For example:
--
--      merge [1,3,5] [2,4,6] == [1,2,3,4,5,6]
--      merge [1,2,6] [1,4,5] == [1,1,2,4,5,6]
--      merge [1,1,6] []      == [1,1,6]

merge :: (Ord a) => [a] -> [a] -> [a]
merge xs []   = xs
merge [] xs   = xs
merge (x:xs) (y:ys)
  | x <= y    = x:y:merge xs ys
  | otherwise = y:x:merge xs ys

--  3. (5%) Write a function "countBy" that's like "count" except it takes an
--     equality predicate as an additional (first) argument.  So in particular,
--     "countBy (==)" should be equivalent to "count".

countBy :: (a -> a -> Bool) -> a -> [a] -> Int
countBy _ _ [] = 0
countBy p a (x:xs)
  | p a x      = 1 + countBy p a xs
  | otherwise  = countBy p a xs

--  4. (5%) Write a function "mergeBy" that's like "merge" except it takes a
--     comparator as an additional (first) argument.  So in particular,
--     "mergeBy compare" should be equivalent to "merge".

mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy _ _ [] = []
mergeBy _ [] _ = []
mergeBy z (x:xs) (y:ys) = case z x y of
  LT -> x:y: mergeBy z xs ys
  EQ -> y:x: mergeBy z xs ys
  GT -> y:x: mergeBy z xs ys

--  5. (10%) Learn about the function "liftM" in the Control.Monad module that
--     comes with Haskell.  (You can just read the source code defining it.)
--     Write a function "liftMBy" that's like "liftM" except it takes a monad's
--     "return" and "(>>=)" as additional (first and second) arguments.  So in
--     particular, "liftMBy return (>>=)" should be equivalent to "liftM".  Be
--     sure to give this "liftMBy" function a type signature, as advised at the
--     top of this file.

liftMBy :: (t3 -> t2) -> (t1 -> (t4 -> t2) -> t) -> (t4 -> t3) -> t1 -> t
liftMBy ret bind f m1 =
  m1 `bind`(\x1 ->
    ret (f x1))

--  6. (10%) Learn about the function "sequence" in Haskell.  For example:
--
--      sequence [[1,2],[3,4,5]] == [[1,3],[1,4],[1,5],[2,3],[2,4],[2,5]]
--
--     Write a function "sequenceBy" that's like "sequence" except it takes a
--     monad's "return" and "(>>=)" as additional (first and second) arguments.
--     So in particular, "sequenceBy return (>>=)" should be equivalent to
--     "sequence".  Be sure to give this "liftMBy" function a type signature,
--     as advised at the top of this file.  You may need the Rank2Types
--     language extension enabled at the top of this file, in order to put
--     "forall a." in the signature.

sequenceBy :: ([t1] -> t) -> (a -> (t1 -> t) -> t) -> [a] -> t
sequenceBy ret bind ls =
  head ls `bind` (\x ->
    last ls `bind` (\y ->
      ret [x,y]))

--  7. (10%) Learn about the function "liftM2" in the Control.Monad module that
--     comes with Haskell.  (You can just read the source code defining it.)
--     Write a function "liftM2By" that's like "liftM2" except it takes a
--     monad's "return" and "(>>=)" as additional (first and second) arguments.
--     So in particular, "liftM2By return (>>=)" should be equivalent to
--     "liftM2".  Be sure to give this "liftM2By" function a type signature, as
--     advised at the top of this file.  You may need the Rank2Types language
--     extension enabled at the top of this file, in order to put "forall a."
--     in the signature.

liftM2By :: (t2 -> t1) -> (t -> (t3 -> t1) -> t1) -> (t3 -> t3 -> t2) -> t -> t -> t1
liftM2By ret bind f m1 m2 =
  m1 `bind` (\x ->
    m2 `bind` (\y ->
      ret (f x y)))

-- Section 2 (20%) -------------------------------------------------------------
-- Parametric polymorphism

--  8. (5%) Write down as many observably different Haskell terms as you can
--     (up to 5 of them) that have the parametrically polymorphic type
--
--      (a -> b) -> a -> b
--
--     Your terms should not cause errors (or undefinedness or nontermination).
--     Name them f1, f2, f3, f4, f5 (or just f1 if there is only one).

f1 :: (a -> b) -> a -> b
f1 = ($)

f2 :: (a -> b) -> a -> b
f2 = ($!)

--  9. (5%) Same as the previous problem, but with the type
--
--      [(Int, a)]
--
--     Name the terms g1, g2, g3, g4, g5 (or just g1 if there is only one).

g1 :: [(Int, a)]
g1 = []

-- 10. (10%) Same as the two previous problems, but with the type
--
--      a -> (Bool -> a -> a) -> a
--
--     Name the terms h1, h2, h3, h4, h5 (or just h1 if there is only one).

h1 :: a -> (Bool -> a -> a) -> a
h1 a f = f True a

h2 :: a -> (Bool -> a -> a) -> a
h2 a f = f False a

h3 :: a -> (Bool -> a -> a) -> a
h3 a _ = a

-- Section 3 (30%) -------------------------------------------------------------
-- Data abstraction

-- To better understand Cook's paper "On understanding data abstraction,
-- revisited" (OOPSLA 2009), let's translate some of the code into Haskell.

-- First let's express abstract data types in Haskell.  Below is the definition
-- of SetImp from Cook's Figure 6.  (The "ADT" suffix on the field names is to
-- avoid name clashes.)  The ExistentialQuantification language extension
-- enabled at the top of this file lets us express Cook's "exists rep.", but
-- Haskell spells it "forall rep.":

data SetImp = forall rep. SetImp {
    emptyADT    :: rep,
    isEmptyADT  :: rep -> Bool,
    insertADT   :: rep -> Int -> rep,
    containsADT :: rep -> Int -> Bool,
    unionADT    :: rep -> rep -> rep }

-- And here's a client that performs some set computations using any given
-- SetImp.  It should return (False,False).

client :: SetImp -> (Bool, Bool)
client (SetImp { emptyADT    = empty,
                 isEmptyADT  = isEmpty,
                 insertADT   = insert,
                 containsADT = contains,
                 unionADT    = union }) =
  let s = empty `insert` 3 `union` (empty `insert` 1) `insert` 5
  in  (isEmpty s, s `contains` 5)

-- 11. (10%) Translate the integer-set implementation from Cook's Figure 2.
--     For example, "client set" should return "(False,False)"
-- data IntegerSet = Empty | Ints Int IntegerSet

set :: SetImp
set = SetImp {
      emptyADT    = [] :: [Int],
      isEmptyADT  = ([] ==),
      insertADT   = flip (:),
      containsADT = flip (elem),
      unionADT    = foldl (flip (:)) }

-- 12. (10%) Translate the integer-set implementation from Cook's Figure 4.
--     For example, "client set2" should return "(False,False)"
--
--     You'll have to fix some typos in Cook's Figure 4: in the three calls to
--     "insert" from "union", the two arguments are swapped.

set2 :: SetImp
set2 = SetImp {
    emptyADT    = [] :: [Int],
    isEmptyADT  = ([] ==),
    containsADT = flip (elem),
    insertADT   = set2Insert,
    unionADT    = set2Union }

set2Insert :: [Int] -> Int -> [Int]
set2Insert s i
  | s == []    = [i]
  | head s > i = i : s
  | otherwise  = head s : set2Insert (tail s) i

set2Union :: [Int] -> [Int] -> [Int]
set2Union = foldl set2Insert

-- Let's turn to expressing objects in Haskell.  Below is the definition of
-- ISet from Cook's Figure 7.  (The "OO" suffix on the field names is to avoid
-- name clashes.)

data ISet = ISet {
    isEmptyOO  :: Bool,
    containsOO :: Int -> Bool,
    insertOO   :: Int -> ISet,
    unionOO    :: ISet -> ISet }

-- We can treat the object-oriented implementation of integer-sets as one
-- particular abstract-data-type implementation of integer-sets, "setOO" below.
-- For example, "client setOO" should return "(False,False)"

setOO :: SetImp
setOO = SetImp {
  emptyADT    = emptyOO,
  isEmptyADT  = isEmptyOO,
  containsADT = containsOO,
  insertADT   = insertOO,
  unionADT    = unionOO }

-- 13. (10%) Translate the integer-set implementation from Cook's Figure 8.
--     Again, "client setOO" should return "(False,False)"
--
--     You'll have to fix some typos in Cook's Figure 8: a call like "s(i)"
--     translates not to "s i" but to "containsOO s i".

-- insertOO = un

emptyOO :: ISet
emptyOO = ISet {
    isEmptyOO  = True,
    containsOO = \_ -> False,
    insertOO   = insertOO fullOO,
    unionOO    = id }
    -- Fixed applyinEmpty = λi. false

-- -- insertH :: Int -> ISet
-- insertH s n = if s `containsOO` n
--                  then s
--                  else ISet { isEmptyOO  = False
--                            , containsOO = \i -> i == n || s `containsOO` i
--                            , insertOO   = insertH setOO
--                            , unionOO    = \a -> unionH a 
--                            }
fullOO = ISet {
  isEmptyOO  = False,
  containsOO = \_ -> True,
  insertOO   = \_ -> fullOO,
  unionOO    = \_ -> fullOO }
