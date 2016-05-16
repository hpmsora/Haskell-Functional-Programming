{-# OPTIONS -W #-}

module HW5 where

{-Won Yong Ha(woha)
  Partner: Brandon Burzon (brburzon) , Simon Lee (sijlee)
-}

-- Welcome to Homework 5: Type/constructor classes.
-- Modify this Haskell code and upload it as a single .hs file.
-- We will grade it for correctness, clarity, and modularity.
-- We might show it in class as an example that everyone can learn from.
-- Late homework will receive half credit if submitted by the next lecture.
-- Work together. List who you worked with. Submit only your own writing.
-- Ask questions during lecture, in online discussion, at office hours.
-- Avoid code duplication where possible by abstracting similar functions.
-- Make sure that your code typechecks by loading it in GHC.
-- Document your code by giving a brief description of each function,
-- and by giving each function a type signature.
-- Don't put junk in your type. Don't jam special cases into your type.

-- Thanks to
--      Ralf Hinze. 2003.  Fun with phantom types.  In The fun of programming,
--      ed. Jeremy Gibbons and Oege de Moor.  Basingstoke: Palgrave Macmillan.
-- for the basis of this homework.

-- Section 1 (60%) -------------------------------------------------------------

-- Suppose you are developing an application where the need arises to compress
-- data to strings of bits.  As it happens, you have data of many different
-- types and you want to program a compression function that works for all of
-- these types.  This is a typical case for Haskell's type classes.

data Bit = O | I
  deriving (Eq)

-- 1. (15%) Instead of deriving Show, define an instance of the Show class for
--    the Bit type above, so
--      "show O"           returns the string "0"
--      "show I"           returns the string "1"
--      "show []"          returns the string "[]"
--      "show [I,O,I,I,O]" returns the string "[10110]"
--    This is useful for producing nicer error messages.

instance Show Bit where
  show O = "0"
  show I = "1"
  showList ls s = showing ls shows s
  
showing :: [a] -> (a -> ShowS) -> ShowS
showing [] _ s = "[]" ++ s
showing (x:xs) showx s = '[' : showx x (showl xs)
  where		    
    showl [] = ']' : s
    showl (y:ys) = showx y (showl ys)

example1_1 = O
example1_2 = I
example1_3 = [I, O, I, I]

-- The basic idea is to define a type class whose instances are types whose
-- values can be compressed.

class Compress a where
  compress   :: a -> [Bit]
  decompress :: [Bit] -> (a, [Bit])

-- The "compress" method takes a value of the compressible type and produces a
-- corresponding string of bits.  The compression must be unambiguous in the
-- sense that no two different values compress to the same string, or even to
-- two strings such that one is a prefix of the other.  The unambiguity makes
-- it possible to write a corresponding "decompress" method, which takes a
-- string of bits, removes a prefix produced by compression, and returns the
-- uncompressed value along with the remainder of the string.  So if the input
-- to "decompress" is a string produced by "compress", then the remainder
-- returned by "decompress" should be the empty string.  For example:

instance Compress Bool where
  compress False   = [O]
  compress True    = [I]
  decompress (O:s) = (False, s) -- so decompress (compress False) == (False, [])
  decompress (I:s) = (True , s) -- so decompress (compress True ) == (True , [])
  decompress s@[]  = error ("Unrecognized Bool " ++ show s)

-- 2. (15%) Write a function to test whether the "compress" and "decompress"
--    methods match up for a given value as described above.  This function is
--    useful for testing.  For example,
--      all compressOK [True, False]
--    should give True.

compressOK :: (Eq a, Compress a) => a -> Bool
compressOK a =  (decompress (compress a)) == (True, [])
             || (decompress (compress a)) == (False, [])

-- 3. (15%) Complete the undefined parts of the following instances.

instance Compress Integer where
  compress n = b : case compare d 0 of
                     EQ -> [O]
                     LT -> I : compress (d+1)
                     GT -> I : compress d
    where (d,m) = divMod n 2
          b | m == 0    = O
            | otherwise = I

  decompress bs = (sum $ zipWith (\b x -> b2i b*2^x) h [0..], t)
    where
      (h, t) = splitAt 1 bs
      b2i O = 0
      b2i I = 1

--  decompress (I:ls) = (1, ls)
--  decompress (O:ls) = (0, ls)
--  decompress [O] = (0, [])
--  decompress [I] = (1, [])
  
--  decompress (n:ns) = if n == I then (1, ns) else (0, ns)
--  decompress s@[]  = error ("Unrecognized Integer " ++ show s)

{-  decompress (n:ns) = if (0 == (mod (length (n:ns)) 2))
  	     	      	 then if (n == I)
  	     	      	    then (1, ns)
			 else
			    (0, ns)
		      else (decompress ns)
  decompress (n:s) = if (1 < length(n:s))
                        then if ((mod (length(n:s)) 2) == 0)
                           then if (n == I)
                                   then (1, s)
                                     else (0, s)
                               else (decompress s)
                            else if (n == I)
                                    then (1, [])
                                else (0, [])-}


instance Compress Char where
  compress     = compress . toInteger . fromEnum
  decompress s = (toEnum (fromInteger i), s')
    where (i,s') = decompress s

instance (Compress a) => Compress [a] where
  compress []     = [O]
  compress (a:as) = I : compress a ++ compress as
  decompress (O:bs) = ([], bs)
  decompress (I:bs) = (a:as, bs'')
    where (a, bs')   = decompress bs
          (as, bs'') = decompress bs'

instance (Compress a, Compress b) => Compress (a,b) where
  compress = undefined
  decompress s = ((a,b), s'')
    where (a, s' ) = decompress s
          (b, s'') = decompress s'

-- 4. (15%) (Save a draft copy of this file before you continue.)
--    Change the type of "decompress" from
--      decompress :: [Bit] -> (a, [Bit])
--    to
--      import Control.Monad.State
--      decompress :: State [Bit] a
--    and rewrite the code above accordingly.  Simplify the code using the fact
--    that
--      State [Bit]
--    is a monad.

-- Section 2 (20%) -------------------------------------------------------------

-- Suppose you have to write a function that traverses a complex data structure
-- representing a university's organizational structure, and that increases the
-- age of a given person.  The interesting part of this function, namely the
-- increase of age, is probably dominated by the boilerplate code that recurs
-- over the data structure.  The boilerplate code is not only tiresome to
-- program, it is also highly vulnerable to changes in the underlying data
-- structure.  Fortunately, generic programming saves the day as it allows us
-- to write the traversal code once and use it many times.

-- Let us first introduce a data type of persons.

type Name   = String
type Age    = Int
data Person = Person Name Age deriving (Eq, Show)

-- Now, the aforementioned function that increases the age can be programmed as
-- follows (this is only the interesting part without the boilerplate code):

type Traversal = Person -> Person

tick :: String -> Traversal
tick s (Person n a) | s == n = Person n (a + 1)
tick _ t                     = t

-- Our goal is to write a function "everywhere" that works on a variety of data
-- structures containing Person, so that
--      everywhere (tick "Richard") [Person "Norma" 50, Person "Richard" 59]
-- gives
--      [Person "Norma" 50,Person "Richard" 60]
-- (because Richard just celebrated his 60th birthday).  This is called a
-- generic traversal -- "generic" because it works on a variety of types;
-- "traversal" because it returns an updated value of the same type.

-- We also want to support a generic query "total", so that the function
-- defined by

type Query a = Person -> a

age :: Query Age
age (Person _ a) = a

-- can be applied throughout a data structure and the results totaled.  For
-- example,
--      total age [Person "Norma" 50, Person "Richard" 59]
-- should give
--      109
-- and it works on a variety of types, not just [Person].

-- It seems to make sense to overload the generic functions "everywhere" and
-- "total" together, so let's define a type class:

class Generic a where
  everywhere :: Traversal -> a -> a
  total      :: Query Int -> a -> Int

-- 5. (10%) Complete the following instance.  (By the way, you can make "total"
--    work for any type that belongs to the Num class, not just Int)

instance Generic Person where
  everywhere = undefined
  total = undefined

-- 6. (10%) Complete the following instance.  (By the way, you can even make it
--    work for any type constructor that belongs to the Functor and Foldable
--    type classes, not just [])

instance (Generic a) => Generic [a] where
  everywhere = undefined
  total      = undefined

-- Section 3 (20%) -------------------------------------------------------------
-- Normalization by evaluation (brain teaser)

-- Let us move on to one of the miracles of theoretical computer science.  In
-- Haskell, one cannot show values of functional types.  For reasons of
-- computability, there is no systematic way of showing functions and any
-- ad-hoc approach would destroy _referential transparency_ (except if "show"
-- were a constant function).  For instance, if "show" yielded the text of a
-- function definition, we could distinguish, say, quick sort from merge sort.
-- Substituting one for the other could then possibly change the meaning of a
-- program.

-- However, what we _can_ do is to print the _normal form_ of a function.  This
-- does not work for Haskell in its full glory, but only for a very tiny
-- subset, the simply typed lambda calculus.  Nonetheless, the ability to do
-- that is rather surprising.

-- Before going into the details, let us consider an example.  Suppose you have
-- defined the following Haskell functions, which correspond to the S, K, and I
-- combinators:

s :: (a -> b -> c) -> (a -> b) -> a -> c
s = \x y z -> (x z) (y z)

k :: a -> b -> a
k = \x _ -> x

i :: a -> a
i = \x -> x

-- and you want to normalize combinator expressions, such as the following.

e :: (a -> a) -> (a -> a)
e = (s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) (k i))

-- The function "reify", defined below, allows you to do that: it takes a
-- Haskell value and yields its normal form.  The type of the Haskell value
-- must be _simple_, meaning built from the Base type (defined below) using the
-- (->) type constructor.  The normal form is given as a function from [Name],
-- which is an infinite list that supplies fresh variable names, to Term, which
-- is an algebraic data type of expressions.

data Term = Var Name | App Term Term | Fun Name Term deriving (Eq, Show)

names :: [Name]
names = [ letter : maybe "" show number
        | number <- Nothing : map Just [1..]
        , letter <- ['a'..'z'] ]

-- For example, evaluating
--      reify (s k k :: Base -> Base) names
-- gives
--      Fun "a" (Var "a")
-- And evaluating
--      reify (s (k k) i :: Base -> Base -> Base) names
-- gives
--      Fun "a" (Fun "b" (Var "a"))
-- Finally, evaluating
--      reify (e :: (Base -> Base) -> (Base -> Base)) names
-- gives
--      Fun "a" (Fun "b" (App (Var "a") (App (Var "a") (Var "b"))))

-- What Fun!  The last test case is probably the most interesting one as the
-- expression "e" is quite involved.  We first use Haskell's type inferencer to
-- determine its type (shown by "e :: (a -> a) -> (a -> a)" above).  Then we
-- call "reify" passing "e" (with the type variable "a" instantiated to
-- "Base").  And there you go: the computed result shows that "e" normalizes to
-- a function that applies its first argument twice to its second.

-- As described above, the function "reify" turns a simply typed Haskell value
-- into a function of type "[Name] -> Term".  It is defined by two instances of
-- a type class "Reify" that follow the definition of a simple type:
--      instance Reify Base where ...
--      instance (Reify a, Reify b) => Reify (a -> b) where ...
-- Let us first consider the latter instance, for function types.  In this
-- case, "reify" has to turn a value of type "a -> b" and a fresh "[Name]"
-- supply into a "Term".  The constructor "Fun" constructs a "Term", so we are
-- left with converting an "a -> b" value to a "Term" for the body of the
-- "Fun".  Suppose that there is a transformation of type "Term -> a"
-- available.  Then we can reflect a "Term" constructed by "Var" to an "a",
-- apply the given "a -> b" function, and finally reify the resulting "b" to a
-- "Term" for the body of the "Fun".  In other words, to implement "reify" we
-- need its converse "reflect", as well.

class Reify a where
  reify   :: a -> ([Name] -> Term)
  reflect :: ([Name] -> Term) -> a

-- Turning to the Base case, this means we require
--      reify   :: Base -> ([Name] -> Term)
-- and its converse
--      reflect :: ([Name] -> Term) -> Base
-- Fortunately, we are still free in the choice of the Base type.  An
-- intriguing option is to define Base as a wrapper equivalent to the type
--      [Name] -> Term

newtype Base = Base ([Name] -> Term)

instance Reify Base where
  reify   (Base v) = v
  reflect v        = Base v

-- 7. (20%) Complete the following instance.

instance (Reify a, Reify b) => Reify (a -> b) where
  reify   = undefined
  reflect = undefined

