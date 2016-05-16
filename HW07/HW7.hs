{-# LANGUAGE Rank2Types, GADTs, StandaloneDeriving #-}
{-# OPTIONS -W #-}
{-

Won Yong Ha

CSCI-C 490
HW7

Partners
 - Brandon Burzon
 - Scott Mathews
 - Simon Lee

Start: March 5 2016
End:   March 7 2016

-}

module HW7 where

-- Welcome to Homework 7: From data types to monads.
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

import Data.Char (toUpper)
--import Data.Binary.Get


-- Section 1 (40%) -------------------------------------------------------------
-- Generalizing algebraic data types

-- Consider the following data types defined and discussed in class.

data ShowList where
  ShowNil  :: ShowList
  ShowCons :: (Show a) => a -> ShowList -> ShowList

data Vec n a where
  VecNil  :: Vec () a
  VecCons :: a -> Vec n a -> Vec [n] a

data Tree a where
  Leaf   :: Tree a
  Branch :: a -> Tree a -> Tree a -> Tree a

deriving instance Show ShowList
deriving instance (Show a) => Show (Vec n a)
deriving instance (Show a) => Show (Tree a)

--  1. (10%) Write functions for these data types that are analogous to the
--     "length" function for Haskell's predefined lists.  For example, the
--     "sizeT" function should return the number of "a"s stored in a "Tree a".

sizeSL :: ShowList -> Int
sizeSL ShowNil = 0
sizeSL (ShowCons _ xs) = 1 + sizeSL xs

sizeV :: Vec n a -> Int
sizeV VecNil = 0
sizeV (VecCons _ a) = 1 + sizeV a

sizeT :: Tree a -> Int
sizeT Leaf = 0
sizeT (Branch _ l r) = 1 + sizeT l + sizeT r

--  2. (10%) Write functions for these data types that are analogous to the
--     "zip" function for Haskell's predefined lists.

zipSL :: ShowList -> ShowList -> ShowList
zipSL ShowNil         ShowNil         = ShowNil
zipSL ShowNil         (ShowCons _ _ ) = ShowNil
zipSL (ShowCons _ _ ) ShowNil         = ShowNil
zipSL (ShowCons x xs) (ShowCons y ys) = ShowCons (x,y) (zipSL xs ys)

zipV :: Vec n a -> Vec n b -> Vec n (a,b)
zipV  VecNil         VecNil        = VecNil
zipV (VecCons x xs) (VecCons y ys) = VecCons (x,y) (zipV xs ys)

zipT :: Tree a -> Tree b -> Tree (a,b)
zipT  Leaf             Leaf            = Leaf
zipT  Leaf            (Branch _ _ _)   = Leaf
zipT (Branch _ _ _)    Leaf            = Leaf
zipT (Branch x xleft xright) (Branch y yleft yright) =
  Branch (x,y) (zipT xleft yleft) (zipT xright yright)

--  3. (10%) Write functions for these data types that are analogous to the
--     "map" function for Haskell's predefined lists.  Whenever possible, make
--     your function the "fmap" method in Haskell's predefined Functor class.

data SomeShow where
  SomeShow :: (Show a) => a -> SomeShow

mapSL :: (SomeShow -> SomeShow) -> ShowList -> ShowList
mapSL _ ShowNil         = ShowNil
mapSL f (ShowCons a sl) =
  let b = f (SomeShow a)
  in case b of
     (SomeShow c) -> ShowCons c (mapSL f sl)

mapV :: (a -> b) -> Vec n a -> Vec n b
mapV = fmap

--f

instance Functor (Vec n) where
  fmap _ VecNil = VecNil
  fmap f (VecCons n' a) = VecCons (f n') (fmap f a)

mapT :: (a -> b) -> Tree a -> Tree b
mapT = fmap

instance Functor Tree where
  fmap _ Leaf = Leaf
  fmap f (Branch a left right)= Branch (f a) (fmap f left) (fmap f right)

--  4. (10%) Combine the ideas behind ShowList and Vec to define a new type
--     constructor ShowVec.  The type constructor ShowVec you define should take
--     just one argument, which represents how many items are stored, but the
--     type of the items should be hidden and may differ from item to item, as
--     long as each type belongs to Show.  For example, the following terms
--     should type-check, and the first two terms should have the same type but
--     not the third:
--
--      ShowVecCons True (ShowVecCons 'a' ShowVecNil)
--      ShowVecCons "hi" (ShowVecCons 'a' ShowVecNil)
--      ShowVecCons True (ShowVecCons 'a' (ShowVecCons "hi" ShowVecNil))
--
--     As in the previous problems, write the analogous of "length", "zip", and
--     "map" for the ShowVec you define.

-- data ShowList where
--   ShowNil  :: ShowList
--   ShowCons :: (Show a) => a -> ShowList -> ShowList

-- data Vec n a where
--   VecNil  :: Vec () a
--   VecCons :: a -> Vec n a -> Vec [n] a

data ShowVec n where
  ShowVecNil  :: ShowVec ()
  ShowVecCons :: (Show a) => a -> ShowVec n -> ShowVec [n]

deriving instance Show (ShowVec n)

sizeSV :: ShowVec n -> Int
sizeSV ShowVecNil = 0
sizeSV (ShowVecCons _ sv) = 1 + sizeSV sv

zipSV :: ShowVec n -> ShowVec n -> ShowVec n
zipSV ShowVecNil ShowVecNil                 = ShowVecNil
zipSV (ShowVecCons a n1) (ShowVecCons b n2) = ShowVecCons (a, b) (zipSV n1 n2)

mapSV :: (SomeShow -> SomeShow) -> ShowVec n -> ShowVec n
mapSV _ ShowVecNil = ShowVecNil
mapSV f (ShowVecCons a n) =
  let fApplyToA = f (SomeShow a)
  in case fApplyToA of
    (SomeShow newA) -> ShowVecCons newA (mapSV f n)

-- Section 2 (40%) -------------------------------------------------------------
-- Custom control structures

-- Consider the following IO action, which keeps reading characters from the
-- input until the character 'Y' or 'N' is encountered (regardless of case).
-- This is handy for asking the user a yes-no question.

--main = yn'

yn :: IO Bool
yn = do c <- getChar
        case toUpper c of 'Y' -> return True
                          'N' -> return False
                          _   -> yn

-- In general, we might want to keep performing an IO action until its result
-- satisfies a predicate.  (A predicate is a function that returns Bool.)  We
-- can create this control structure in Haskell without changing the language:

validate :: (a -> Bool) -> IO a -> IO a
validate f m = do x <- m
                  if f x then return x else validate f m

--  5. (10%) Express "yn" in terms of "validate", without any more recursion.

--import Data.Binary.Bits.Get

yn' :: IO Bool
yn' = validate id getBool

--ynPred :: Char -> Bool
--ynPred c = if bigC == 'Y'
--           then True
--           else if bigC == 'N'
--                then False
--                else False
--  where bigC = toUpper c

getBool :: IO Bool
getBool = do c <- getChar
  	     case toUpper c of 'Y' -> return True
   	 	      	       'N' -> return True
		     	       _   -> return False


-- Although "validate" is useful in this way, it throws away all the information
-- from the hard work done by the validation predicate, leaving only a decision
-- between acceptance and rejection.  Hence, your "yn'" probably duplicates
-- the work of converting Char to Bool.  This kind of wasteful information
-- bottleneck is sometimes called "Boolean blindness".

--  6. (10%) Create a control structure "normalize" that keeps performing an IO
--     action as long as feeding its result to the given validation function
--     yields Nothing.

normalize :: (a -> Maybe b) -> IO a -> IO b
normalize f m = do c <- m
	      	   case f c of Just b -> return b
		   	       Nothing -> normalize f m

--  7. (10%) Express "validate" in terms of "normalize", without any more
--     recursion.

--validate' :: (a -> Bool) -> IO a -> IO a
--validate' f m = normalize $ \x ->
--	      		       case f x of True	-> Just x
--			    	     	   False -> Nothing
--validate' f = do x <- m
--	      	 if fx

--val2_helper :: a -> Maybe b
--va
--val2_helper c = normalize

validate' :: (a -> Bool) -> IO a -> IO a
validate' f = normalize $ \x ->
                          case f x of True -> Just x
                                      False -> Nothing


--  8. (10%) Express "yn" in terms of "normalize" directly, without any more
--     recursion or duplicated work.

--yn'' :: IO Bool
--yn'' = normalize validate' getChar

yn'' :: IO Bool
yn'' = normalize isYN $ validate' toBool getChar

isYN :: Char -> Maybe Bool
isYN a = case toUpper a of 'Y' -> Just True
                           'N' -> Just True
                           _  -> Nothing

toBool :: Char -> Bool
toBool a = case toUpper a of 'Y' -> True
                             'N' -> True
                             _  -> False

-- Section 3 (20%) -------------------------------------------------------------
-- Operational semantics

-- Peyton Jones's operational semantics helps us understand IO programs and
-- explain them to each other.  The simplest version of this operational
-- semantics (presented in Sections 3.2-3.4) defines "transitions" from one
-- program state P to another program state Q.  Each transition is labelled
-- by some "alpha" to indicate what kind of transition it is and what happens
-- during the transition, whether observable (such as putting a character) or
-- unobservable.  The same starting state might allow multiple transitions to
-- different states (as when we are getting a character and it could be any
-- character) or to no state (as when the program has finished and the state has
-- the form "return (...)").

-- We can define the following data types to represent a sequence of
-- transitions.  We take advantage of Haskell's type system to check that
-- all the states have the same type, but not that the states are actually
-- related by the purported transition labels.

data Transcript a = Return a | Transition (IO a) Transition (Transcript a)
data Transition   = PUTC Char | GETC Char | LUNIT | FUN deriving (Eq, Show)

-- For example, we represent the running example in Section 3.4 like this:

transcript1 :: Transcript ()
transcript1 = Transition (getChar >>= \x -> putChar (toUpper x))
                         (GETC 'w')
            $ Transition (return 'w' >>= \x -> putChar (toUpper x))
                         LUNIT
            $ Transition ((\x -> putChar (toUpper x)) 'w')
                         FUN
            $ Transition (putChar 'W')
                         (PUTC 'W')
            $ Return ()

--  9. (10%) Complete the following transition sequence.

transcript2 :: Transcript (Char, Char)
transcript2 = Transition (return getChar >>= \m ->
                          m >>= \x -> m >>= \y -> return (x,y))
                         LUNIT
            $ Transition ((\m -> m >>= \x -> m >>= \y -> return (x,y)) getChar)
                         FUN
            $ Transition (getChar >>= \x -> getChar >>= \y -> return (x,y))
                         (GETC 'w')
            $ Transition (return 'w' >>= \x -> getChar >>= \y -> return (x,y))
                         LUNIT
            $ Transition ((\x -> getChar >>= \y -> return (x,y)) 'w')
                         FUN
            $ Transition (getChar >>= \y -> return ('w',y))
                         (GETC 'x')
            $ Transition (return 'x' >>= \y -> return ('w',y))
                         LUNIT
            $ Transition ((\y -> return ('w',y)) 'x')
                         FUN
            $ Return ('w', 'x')

-- 10. (10%) Complete the following transition sequence.

transcript3 :: Transcript (Char, Char)
transcript3 = Transition (getChar >>= \c ->
                          return c >>= \x -> return c >>= \y -> return (x,y))
                         (GETC 'w')
            $ Transition (return 'w' >>= \c ->
                          return c >>= \x -> return c >>= \y -> return (x,y))
                         LUNIT
            $ Transition ((\c ->
                          return c >>= \x -> return c >>= \y -> return (x,y)) 'w')
                         FUN
            $ Transition (return 'w' >>= \x -> return 'w' >>= \y -> return (x,y))
                         LUNIT
            $ Transition ((\x -> return 'w' >>= \y -> return (x,y)) 'w')
                         FUN
            $ Transition (return 'w' >>= \y -> return ('w',y))
                         LUNIT
            $ Transition ((\y -> return ('w',y)) 'w')
                         FUN
            $ Return ('w','w')