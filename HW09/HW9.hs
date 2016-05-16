{-# OPTIONS -W #-}
{-
Brandon Burzon
Simon Lee
Won Yong Ha
Scott Mathews
-}
module HW9 where

-- Welcome to Homework 9: Staging and code generation.
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

import Control.Monad.State (State, state, runState)

-- Section 1 (30%) -------------------------------------------------------------
-- Generalizing and staging "power"

-- A monoid is a type "a" that comes with a binary operation (in other words,
-- a function of type "a -> a -> a") that is similar to addition in two ways.
-- First, it is associative (so x+(y+z)=(x+y)+z for all x,y,z).  Second, it has
-- an identity element (like 0 for addition, so 0+x=x+0=x for all x).  Haskell's
-- standard library defines a type class "Monoid".  The binary operation is
-- "mappend" and its identity element is "mempty".

import Data.Monoid

-- To understand monoids better, you can find many instances of "Monoid" in
-- the "Data.Monoid" module.  Here's a fancier example: suppose we want to
-- repeatedly apply a function from the integers {1,...,30} to the integers
-- {1,...,30}.  (Maybe 30 is the number of states in a finite-state machine --
-- see http://blog.sigfpe.com/2009/01/fast-incremental-regular-expression.html
-- for more on this application.)  We can represent this function as an array
-- of 30 integers in {1,...,30}.  These functions form a monoid, whose binary
-- operation is function composition and whose identity element is the identity
-- function.  A permutation, such as "myPermutation" below, is a bijective
-- function.

import Data.Array

newtype Table = Table (Array Int Int) deriving (Eq, Show)

listTable :: [Int] -> Table
listTable js = Table (listArray (1,30) js)

myPermutation :: Table
myPermutation = listTable [ 2, 3, 4, 5, 1, 7, 6,10, 8, 9,
                           12,13,14,15,16,17,11,18,29,19,
                           20,21,22,23,24,25,26,27,28,30]

funTable :: (Int -> Int) -> Table
funTable f = listTable (map f [1..30])

instance Monoid Table where
  mempty                      = funTable id
  mappend (Table a) (Table b) = funTable ((a !) . (b !))

-- Given a non-negative integer "n" and a monoid element "x", we can mappend
-- x to itself n times.  This operation is to mappend as multiplication is to
-- addition.

mtimes :: (Monoid a) => Int -> a -> a

mtimes 0 _ = mempty
mtimes n x = mappend (mtimes (n-1) x) x
{-# INLINE mtimes #-}

-- A special case of "mtimes" is "power", as the code below shows.

power :: (Num a) => Int -> a -> a
power n x = getProduct (mtimes n (Product x))

-- The order of a permutation is how many times we have to repeat it to get the
-- identity permutation.  For example, "order myPermutation" computes 2310.

order :: (Eq a, Monoid a) => a -> Int
order x = head [ i | i <- [1..], mtimes i x == mempty ]

-- 1. (10%) Stage "mtimes", so that all the computation and recursion using its
--    first argument "n" happens independently of the second argument "x".  Using
--    this algorithm in "power" above should let you raise many numbers to the
--    same power faster.

mtimesStaged :: (Monoid a) => Int -> a -> a
mtimesStaged 0 = \_ -> mempty
mtimesStaged 1 = id
mtimesStaged n = let f = mtimesStaged (n - 1)
                 in \x -> mappend (f x) x
{-# INLINE mtimesStaged #-}
-- This is the correct form of it. It's possible we see no improvment
-- because the compiler is already doing it for us in mtimes ?

-- 2. (10%) Generalize the repeated-squaring "power" algorithm from class to
--    implement a faster version of "mtimes".  Using this algorithm in "order"
--    above should let you compute "order myPermutation" faster.

mtimes' :: (Monoid a) => Int -> a -> a
mtimes' 0 _ = mempty
mtimes' 1 x = x
mtimes' n x = case 2 `divMod` n of
  (q, 0) -> double (mtimes' q x)
  _      -> mappend (mtimes' (n - 1) x) x
  where double x = mappend x x

ntimes' :: Int -> Int -> Int
ntimes' 0 _ = 0
ntimes' 1 x = x
ntimes' n x = case 2 `divMod` n of
  (q, 0) -> double (ntimes' q x)
  _      -> (ntimes' (n - 1) x) + x
  where double x = x + x

power' :: (Num a) => Int -> a -> a
power' n x = getProduct (mtimes' n (Product x))

-- 3. (10%) Stage your "mtimes'", so that all the computation and recursion
--    using its first argument "n" happens independently of the second argument
--    "x".  Using this algorithm in "power" above should let you raise many
--    numbers to the same power even faster.

mtimes'Staged :: (Monoid a) => Int -> a -> a
mtimes'Staged 0 = \_ -> mempty
mtimes'Staged 1 = \x -> x
mtimes'Staged n = case 2 `divMod` n of
  (q, 0) -> let f = mtimes'Staged q in \x -> sqr (f x)
  _      -> let g = mtimes'Staged (n-1) in \x -> mappend (g x) x
  where sqr x = mappend x x

-- Section 2 (40%) -------------------------------------------------------------
-- Staging an interpreter

-- Recall the following interpreter for a simple programming language with
-- numbers, booleans, and functions.

data Term = Int Integer
          | Sub Term Term
          | Less Term Term
          | If Term Term Term
          | Var Name
          | Let Name Term Term
          | Lam Name Term
          | App Term Term
    deriving (Show)

data Value = N { nOf :: Double }
           | B { bOf :: Bool }
           | F { fOf :: Value -> Value }

eval :: Term -> Env Value -> Value
eval (Int i)       _   = N (fromInteger i)
eval (Sub e1 e2)   env = N (nOf (eval e1 env) - nOf (eval e2 env))
eval (Less e1 e2)  env = B (nOf (eval e1 env) < nOf (eval e2 env))
eval (If e0 e1 e2) env = eval (if bOf (eval e0 env) then e1 else e2) env
eval (Var v)       env = lookupEnv v env
eval (Let v e1 e0) env = eval e0 (extendEnv v (eval e1 env) env)
eval (Lam v e0)    env = F (\a -> eval e0 (extendEnv v a env))
eval (App e0 e1)   env = fOf (eval e0 env) (eval e1 env)

add :: Term -> Term -> Term
add e1 e2 = Sub e1 (Sub (Int 0) e2)

type Name = String

type Env a = [(Name, a)]

emptyEnv :: Env a
emptyEnv = []

lookupEnv :: Name -> Env a -> a
lookupEnv n []           = error ("Unbound variable " ++ n)
lookupEnv n ((n',a):env) = if n == n' then a else lookupEnv n env

extendEnv :: Name -> a -> Env a -> Env a
extendEnv n a env = (n,a):env

-- Let's stage this interpreter so that the same term, in the scope of the same
-- variable names, can be evaluated faster against a variety of variable values.
-- For example, we might want to evaluate the term (add (Var "x") (Var "y")) in
-- the scope of the variable names ["x","y"] faster against a variety of values
-- for the two variables.  This way, we can choose longer variable names without
-- worrying about run-time performance.

-- One challenge is that the environment (the second argument to "eval") is a
-- mix of the static (variable names) and the dynamic (variable values).  So in
-- order to stage "eval", we first have to split the environment into a static
-- part and a dynamic part.  Static and dynamic are called different binding
-- times, and this split is a kind of binding-time improvement.

type StaticEnv  = [Name]
type DynamicEnv = [Value]

-- 4. (10%) Split the environment argument to "lookupEnv" above into a static
--    part (containing variable names) and a dynamic part (containing variable
--    values).  Your definition of "lookupEnvSplit" should satisfy
--      lookupEnvSplit n s d = lookupEnv n (zip s d)
--    whenever s and d are of equal length.

lookupEnvSplit :: Name -> StaticEnv -> DynamicEnv -> Value
lookupEnvSplit n []     []    = error ("Unbound variable " ++ n)
lookupEnvSplit n (n':s) (a:d) = if n == n'
                                then a
                                else lookupEnvSplit n s d

-- 5. (15%) Split the environment argument to "eval" above into a static part
--    (containing variable names) and a dynamic part (containing variable
--    values).  Your definition of "evalSplit" should satisfy
--      evalSplit e s d = eval e (zip s d)
--    whenever s and d are of equal length.

evalSplit :: Term -> StaticEnv -> DynamicEnv -> Value
evalSplit (Int i)       _ _ = N (fromInteger i)
evalSplit (Sub e1 e2)   s d = N (nOf (evalSplit e1 s d) - nOf (evalSplit e2 s d))
evalSplit (Less e1 e2)  s d = B (nOf (evalSplit e1 s d) < nOf (evalSplit e2 s d))
evalSplit (If e0 e1 e2) s d = evalSplit (if bOf (evalSplit e0 s d)
                                         then e1 else e2) s d
evalSplit (Var v)       s d = lookupEnvSplit v s d
evalSplit (Let v e1 e0) s d = evalSplit e0 ([v] ++ s) ([(evalSplit e1 s d)] ++ d)
evalSplit (Lam v e0)    s d = F (\a -> evalSplit e0 ([v] ++ s) ([a] ++ d))
evalSplit (App e0 e1)   s d = fOf (evalSplit e0 s d) (evalSplit e1 s d)

-- eval (Less e1 e2)  env = B (nOf (eval e1 env) < nOf (eval e2 env))
-- eval (If e0 e1 e2) env = eval (if bOf (eval e0 env) then e1 else e2) env
-- eval (Var v)       env = lookupEnv v env
-- eval (Let v e1 e0) env = eval e0 (extendEnv v (eval e1 env) env)
-- eval (Lam v e0)    env = F (\a -> eval e0 (extendEnv v a env))
-- eval (App e0 e1)   env = fOf (eval e0 env) (eval e1 env)

-- 6. (15%) Stage your "lookupEnvSplit" and "evalSplit", so that all the
--    computation and recursion using the first two arguments (the term and
--    the static environment) happens independently of the third argument (the
--    dynamic environment).

lookupEnvStaged :: Name -> StaticEnv -> DynamicEnv -> Value
lookupEnvStaged n []     = \_ -> error ("Unbound variable " ++ n)
lookupEnvStaged n (n':s) = let f = lookupEnvStaged n s
                           in if n == n'
                              then \(a:d) -> a
                              else \(a:d) -> f d

-- lookupEnvSplit :: Name -> StaticEnv -> DynamicEnv -> Value
-- lookupEnvSplit n []     []    = error ("Unbound variable " ++ n)
-- lookupEnvSplit n (n':s) (a:d) = if n == n'
--                                 then a
--                                 else lookupEnvSplit n s d

evalStaged :: Term -> StaticEnv -> DynamicEnv -> Value
evalStaged (Int i)       _ = \_ -> N (fromInteger i)
evalStaged (Sub e1 e2)   s = let c1 = evalStaged e1 s
                                 c2 = evalStaged e2 s
                             in \d -> N (nOf (c1 d) - nOf (c2 d))
evalStaged (Less e1 e2)  s = let c1 = evalStaged e1 s
                                 c2 = evalStaged e2 s
                             in \d -> B (nOf (c1 d) < nOf (c2 d))
evalStaged (If e0 e1 e2) s = let c1 = evalStaged e0 s
                             in \d -> evalStaged (if bOf (c1 d)
                                                  then e1
                                                  else e2) s d
evalStaged (Var v)       s = lookupEnvStaged v s
evalStaged (Let v e1 e0) s = let c1 = evalStaged e1 s
                             in \d -> evalStaged e0 ([v] ++ s) ([(c1 d)] ++ d)
evalStaged (Lam v e0)    s = let c1 = evalStaged e0 ([v] ++ s)
                             in \d -> F (\a -> c1 ([a] ++ d))
evalStaged (App e0 e1)   s = let c1 = evalStaged e0 s
                                 c2 = evalStaged e1 s
                             in \d -> fOf (c1 d) (c2 d)

-- evalSplit (Less e1 e2)  s d = B (nOf (evalSplit e1 s d) < nOf (evalSplit e2 s d))
-- evalSplit (If e0 e1 e2) s d = evalSplit (if bOf (evalSplit e0 s d)
--                                          then e1 else e2) s d
-- evalSplit (Var v)       s d = lookupEnvSplit v s d
-- evalSplit (Let v e1 e0) s d = evalSplit e0 ([v] ++ s) ([(evalSplit e1 s d)] ++ d)
-- evalSplit (Lam v e0)    s d = F (\a -> evalSplit e0 ([v] ++ s) ([a] ++ d))
-- evalSplit (App e0 e1)   s d = fOf (evalSplit e0 s d) (evalSplit e1 s d)


-- You can compare the performance of
--      eval (or rather, (\e s d -> eval e (zip s d)))
--      evalSplit
--      evalStaged
-- by passing them to a function such as the following, especially if you also
-- pass very long variable names.  In addition to Int and Sub and Var, try using
-- the Term constructs you just implemented, such as Let and Lam and App!

try :: (Term -> StaticEnv -> DynamicEnv -> Value) -> Name -> Name -> Double
try evalS x y = let f = evalS (add (Var x) (Var y)) [x,y]
                in sum [nOf (f [N x, N y]) | x <- [1..1000], y <- [1..1000]]

-- Section 3 (30%) -------------------------------------------------------------
-- Code generation without code duplication

-- Functions like "power" and "power'" above can be used to generate code to be
-- separately compiled for higher performance.  Generating code to be separately
-- compiled for higher performance is sometimes called "offshoring".

-- As we saw in class, thanks to the polymorphism in "power" and "power'", we can
-- offshore them simply by defining a type for code expressions along with an
-- instance of Num.

-- 7. (10%) Complete the "instance Num IntCode" below, so that "power" and
--    "power'" above can generate expressions in C.  For example, "test7" below
--    should compute "True".

newtype IntCode = IntCode String deriving (Eq, Show)

instance Num IntCode where
  IntCode x * IntCode y = IntCode ("(" ++ x ++ "*" ++ y ++ ")")
  fromInteger = \x -> IntCode (show x)

test7 :: Bool
test7 = power  10 (IntCode "x")
        == IntCode "((((((((((1*x)*x)*x)*x)*x)*x)*x)*x)*x)*x)"
     && power' 10 (IntCode "x")
        == IntCode "((((x*x)*(x*x))*x)*(((x*x)*(x*x))*x))"

-- The problem with offshoring "power'" is that it generates code that performs
-- too many multiplications.  Even though the original algorithm squares the
-- input x only once, the generated code
--      ((((x*x)*(x*x))*x)*(((x*x)*(x*x))*x))
-- squares x four times!  The problem is that the generator, instead of
-- duplicating the result of code, duplicates the code itself.  To fix this
-- problem, we need to generate C code that defines local variables.  For
-- example, for raising numbers to the 10th power, we want to generate
--      int power(int x) {
--        int t0 = (x*x);
--        int t1 = (t0*t0);
--        int t2 = (t1*x);
--        int t3 = (t2*t2);
--        return t3;
--      }
-- so that the square of x is computed only once and stored in t0 for reuse.

-- It turns out that monads are a good tool for generating code that defines
-- local variables.  We can use a state monad to keep track of the local
-- variables defined by a code generator.

type M = State [IntCode]

-- The crucial action in the monad is to define a new local variable and
-- produce its name as a new code expression.  This action is "insert_let".

-- 8. (10%) Define "insert_let" below to add a code expression to the end of the
--    list stored by the monad "M".  These local variables are all of type "int"
--    in C, and their names are "t0", "t1", "t2", ...  For example, "test8"
--    below should compute "True".

insert_let :: IntCode -> M IntCode
insert_let code = state (\bindings -> (code, bindings ++ return code))


offshore :: (IntCode -> M IntCode) -> String
offshore f = let (IntCode result, bindings) = runState (f (IntCode "x")) []
                 bind i (IntCode rhs) = "int t" ++ show i ++ " = " ++ rhs ++ ";"
             in unlines (  "int power(int x) {"
                        :  map ("  " ++) (  zipWith bind [0..] bindings
                                         ++ ["return " ++ result ++ ";"]  )
                        ++ ["}"]  )

test8 :: Bool
test8 = offshore (return . power 10)
        == "int power(int x) {\n\
           \  return ((((((((((1*x)*x)*x)*x)*x)*x)*x)*x)*x)*x);\n\
           \}\n"
     && offshore (return . power' 10)
        == "int power(int x) {\n\
           \  return ((((x*x)*(x*x))*x)*(((x*x)*(x*x))*x));\n\
           \}\n"
     && offshore (\x -> do x2 <- insert_let (x*x)
                           y  <- insert_let 42
                           return ((x2*x2)*y))
        == "int power(int x) {\n\
           \  int t0 = (x*x);\n\
           \  int t1 = 42;\n\
           \  return ((t0*t0)*t1);\n}\n"
     && offshore (\x -> do x2 <- insert_let (x*x)
                           x4 <- insert_let (x2*x2)
                           x8 <- insert_let (x4*x4)
                           return (x8*x2))
        == "int power(int x) {\n\
           \  int t0 = (x*x);\n\
           \  int t1 = (t0*t0);\n\
           \  int t2 = (t1*t1);\n\
           \  return (t2*t0);\n}\n"

test1 = offshore (\x -> do x2 <- insert_let (x*x)
                           x4 <- insert_let (x2*x2)
                           x8 <- insert_let (x4*x4)
                           return (x8*x2))


-- 9. (10%) Define "power''" below to generate C code that raises numbers to
--    the given power by repeated squaring.  The generated code should perform
--    the same algorithm as "power'" but introduce a local variable for each
--    multiplication.  For example, "test9" below should compute "True".

power'' :: Int -> IntCode -> M IntCode
power'' 0 _ = return 0
power'' 1 x = return x
power'' n x = undefined

  -- case 2 `divMod` n of
  -- (q, 0) -> let f = power'' q in do x1 <- insert_let (x*x)
  --                                   return x1
  -- _      -> let g = power'' (n-1) in do x2 <- insert_let (x*x)
                                        -- g x2

-- insert_let :: IntCode -> M IntCode
-- insert_let code = state (\bindings -> (code, bindings))

test9 :: Bool
test9 = offshore (power'' 10)
        == "int power(int x) {\n\
           \  int t0 = (x*x);\n\
           \  int t1 = (t0*t0);\n\
           \  int t2 = (t1*x);\n\
           \  int t3 = (t2*t2);\n\
           \  return t3;\n\
           \}\n"
     && offshore (power'' 42)
        == "int power(int x) {\n\
           \  int t0 = (x*x);\n\
           \  int t1 = (t0*t0);\n\
           \  int t2 = (t1*x);\n\
           \  int t3 = (t2*t2);\n\
           \  int t4 = (t3*t3);\n\
           \  int t5 = (t4*x);\n\
           \  int t6 = (t5*t5);\n\
           \  return t6;\n\
           \}\n"
