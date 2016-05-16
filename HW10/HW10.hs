 {-# OPTIONS -W #-}

module HW10 where

{-

Won Yong Ha

Collaborate: Brandon Burzon, Scott Mathew, Simon Lee

Start: 17 April 2016
End: 18 April 2016

-}

-- Welcome to Homework 10: Hygiene.
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

import Text.Show.Functions ()
import qualified Data.Set as S
import Control.Monad.Cont (Cont, cont, runCont)

-- Recall the simple language below.  In this homework, we'll use staging to
-- generate straight-line code in it.  We derive a Show instance automatically,
-- but if the generated code gets big and you want it nicely indented, you can
-- use Text.Show.Pretty.ppDoc from the pretty-show package on Hackage.

data Term = Int Integer
          | Sub Term Term
          | Mul Term Term
          | Less Term Term
          | If Term Term Term
          | Var Name
          | Let Name Term Term
          | Lam Name Term
          | App Term Term
    deriving (Show, Eq)

data Value = N { nOf :: Double }
           | B { bOf :: Bool }
           | F { fOf :: Value -> Value }
    deriving (Show)

eval :: Term -> Env Value -> Value
eval (Int i)       _   = N (fromInteger i)
eval (Sub e1 e2)   env = N (nOf (eval e1 env) - nOf (eval e2 env))
eval (Mul e1 e2)   env = N (nOf (eval e1 env) * nOf (eval e2 env))
eval (Less e1 e2)  env = B (nOf (eval e1 env) < nOf (eval e2 env))
eval (If e0 e1 e2) env = eval (if bOf (eval e0 env) then e1 else e2) env
eval (Var v)       env = lookupEnv v env
eval (Let v e1 e0) env = eval e0 (extendEnv v (eval e1 env) env)
eval (Lam v e0)    env = F (\a -> eval e0 (extendEnv v a env))
eval (App e0 e1)   env = fOf (eval e0 env) (eval e1 env)

type Name = String

type Env a = [(Name, a)]

emptyEnv :: Env a
emptyEnv = []

lookupEnv :: Name -> Env a -> a
lookupEnv n []           = error ("Unbound variable " ++ n)
lookupEnv n ((n',a):env) = if n == n' then a else lookupEnv n env

extendEnv :: Name -> a -> Env a -> Env a
extendEnv n a env = (n,a):env

fv :: Term -> S.Set Name
fv (Int _)       = S.empty
fv (Sub e1 e2)   = fv e1 `S.union` fv e2
fv (Mul e1 e2)   = fv e1 `S.union` fv e2
fv (Less e1 e2)  = fv e1 `S.union` fv e2
fv (If e0 e1 e2) = fv e0 `S.union` fv e1 `S.union` fv e2
fv (Var v)       = S.singleton v
fv (Let v e1 e0) = fv e1 `S.union` (v `S.delete` fv e0)
fv (Lam v e0)    = v `S.delete` fv e0
fv (App e1 e2)   = fv e1 `S.union` fv e2

nameSupply :: [Name]
nameSupply = map ('x':) (map show [0..])

gensym :: S.Set Name -> [Name]
gensym s = [ n | n <- nameSupply, not (S.member n s) ]

-- Section 1 (40%) -------------------------------------------------------------
-- First-order abstract syntax (FOAS)

-- The following code generator implements a "power" algorithm that's slightly
-- different from what we've been seeing in this course, but just as efficient.

-- from capture.hs
power5 :: Term -> Term
power5 x = let env :: S.Set Name
               env = fv x
               (y:z:[]) = take 2 $ gensym env
           in  Let y (Mul x x)
               $ Let z (Mul (Var y) (Var y))
               $ Mul x (Var z)


powerT :: Int -> Term -> Term
powerT 0 _ = Int 1
powerT 1 x = x
powerT n x =
  let env :: S.Set Name
      env = fv x
      (y:z:[]) = take 2 $ gensym env in
    let (q,r) = n `divMod` 2 in
        Let y (x `Mul` x) $
        let z = powerT q (Var y) in
            if r == 0 then z else z `Mul` x

-- Here's how you can use it to generate a function:
--      powerTfun 5 "x"
-- The Haskell String argument "x" is the argument name of the generated Lam.
-- For example, "test0" below should compute "True".

powerTfun :: Int -> Name -> Term
powerTfun n x = Lam x (powerT n (Var x))

test0 :: Bool
test0 = 32 == nOf (fOf (eval (powerTfun 5 "x") emptyEnv) (N 2))

-- 1. (20%) Actually, powerT is broken because it generates bindings that
--    accidentally capture variable names.  Show this in two ways.  First,
--    set "brokenX" below to an argument name that makes powerTfun generate
--    incorrect code.  Second, set "brokenN" below to an exponent that makes
--    powerTfun generate incorrect code.  Overall, "test1" below should compute
--    "[False,False]".

brokenX :: String
brokenX = "y"

brokenN :: Int
brokenN = 10

test1 :: [Bool] -- make it compute [False,False] first!
test1 = [     32    == nOf (fOf (eval (powerTfun 5  brokenX ) emptyEnv) (N 2))
        , 2^brokenN == nOf (fOf (eval (powerTfun brokenN "x") emptyEnv) (N 2))
        ]

-- 2. (20%) Fix the problem you just showed, by changing "powerT" above to use
--    "gensym" and "fv".  Only change the variable names generated by "powerT".
--    Don't affect the rest of the generated code!
--
--    You should probably write some code to test that you've fixed the problem.
--    To start with, "test1" above should compute "[True,True]" instead.

-- Section 2 (60%) -------------------------------------------------------------
-- Higher-order abstract syntax (HOAS)

-- The following code from class defines a type "E" that wraps around the type
-- "Term" above, along with "smart constructors" that take over generating
-- fresh variable names.

newtype E = E { unE :: [Name] -> Term }

int :: Integer -> E
int i = E (\_ -> Int i)

add :: E -> E -> E
add e1 e2 = E (\fresh -> Sub (unE e1 fresh) (Sub (Int 0) (unE e2 fresh)))

sub :: E -> E -> E
sub e1 e2 = E (\fresh -> Sub (unE e1 fresh) (unE e2 fresh))

mul :: E -> E -> E
mul e1 e2 = E (\fresh -> Mul (unE e1 fresh) (unE e2 fresh))

app :: E -> E -> E
app e1 e2 = E (\fresh -> App (unE e1 fresh) (unE e2 fresh))

let_ :: E -> (E -> E) -> E
let_ e1 f = E (\fresh@(n:fresh') -> Let n (unE e1 fresh)
                                        (unE (f (E (\_ -> Var n))) fresh'))

-- After we finish generating a complete program, of type "E", we can pass it
-- to the "runE" function below to recover a Term we can "show" or "eval".

runE :: E -> Term
runE e = unE e nameSupply

-- For example, the "powerE" function below is like "powerT" above but
-- generates "E" instead of "Term".  Try
--      runE (powerE 5 (int 2))
-- to generate code that computes 2^5=32.

powerE :: Int -> E -> E
powerE 0 _ = int 1
powerE 1 x = x
powerE n x = let (q,r) = n `divMod` 2 in
             let_ (x `mul` x) $ \y ->
             let z = powerE q y in
             if r == 0 then z else z `mul` x

-- To take another example, the "gibE" function below generates code to compute
-- the "Gibonacci sequence", which generalizes the Fibonacci sequence.  The
-- recursive mathematical definition of the Gibonacci sequence is as follows.

gib :: (Num a) => Int -> a -> a -> a
gib 0 a _ = a
gib 1 _ b = b
gib n a b = gib (n-2) a b + gib (n-1) a b

-- But the following generator produces more efficient code.  Try
--      runE (gibE 5 (int 10) (int 100))
-- to generate code that computes gib 5 10 100 = 530.

gibE :: Int -> E -> E -> E
gibE 0 a _ = a
gibE n a b = gibE' (n-1) a b (\_ result -> result)

gibE' :: Int -> E -> E -> (E -> E -> E) -> E
gibE' 0 a b c = c a b
gibE' n a b c = gibE' (n-1) a b $ \x y ->
                let_ (x `add` y) $ \z ->
                c y z

-- 3. (20%) Define the smart constructor "lam" to generate a Lam Term using a
--    fresh variable name.  Your definition should let us generate functions
--    that compute "power n x" and "gib n a b" for a given n but arbitrary
--    x,a,b.  For example, test3 should compute "[True,True,True,True]".

lam :: (E -> E) -> E
lam f = E (\fresh@(n:fresh') ->
             Lam n
             (unE (f (E (\_ -> Var n))) fresh'))

test3 :: [Bool]
test3 = [  runE (lam (\x -> powerE 5 x))
        == (Lam "x0" $
            Let "x1" (Mul (Var "x0") (Var "x0")) $
            Mul (Let "x2" (Mul (Var "x1") (Var "x1")) $
                 Var "x2")
                (Var "x0"))
        ,  runE (lam (\x -> powerE 10 x))
        == (Lam "x0" $
            Let "x1" (Mul (Var "x0") (Var "x0")) $
            Let "x2" (Mul (Var "x1") (Var "x1")) $
            Mul (Let "x3" (Mul (Var "x2") (Var "x2")) $
                 Var "x3")
                (Var "x1"))
        ,  runE (lam (\a -> lam (\b -> gibE 5 a b)))
        == (Lam "x0" $
            Lam "x1" $
            Let "x2" (Sub (Var "x0") (Sub (Int 0) (Var "x1"))) $
            Let "x3" (Sub (Var "x1") (Sub (Int 0) (Var "x2"))) $
            Let "x4" (Sub (Var "x2") (Sub (Int 0) (Var "x3"))) $
            Let "x5" (Sub (Var "x3") (Sub (Int 0) (Var "x4"))) $
            Var "x5")
        ,  runE (lam (\a -> lam (\b -> gibE 10 a b)))
        == (Lam "x0" $
            Lam "x1" $
            Let "x2" (Sub (Var "x0") (Sub (Int 0) (Var "x1"))) $
            Let "x3" (Sub (Var "x1") (Sub (Int 0) (Var "x2"))) $
            Let "x4" (Sub (Var "x2") (Sub (Int 0) (Var "x3"))) $
            Let "x5" (Sub (Var "x3") (Sub (Int 0) (Var "x4"))) $
            Let "x6" (Sub (Var "x4") (Sub (Int 0) (Var "x5"))) $
            Let "x7" (Sub (Var "x5") (Sub (Int 0) (Var "x6"))) $
            Let "x8" (Sub (Var "x6") (Sub (Int 0) (Var "x7"))) $
            Let "x9" (Sub (Var "x7") (Sub (Int 0) (Var "x8"))) $
            Let "x10" (Sub (Var "x8") (Sub (Int 0) (Var "x9"))) $
            Var "x10")
        ]

-- From here on, to ensure hygiene, don't call Term constructors directly such
-- as Int, Sub, Var, Let, Lam.  Instead, call the smart constructors int, add,
-- sub, let_, lam.

-- To make it easier to generate code that defines local variables, we can
-- introduce a monad M, like on the previous homework.  But due to higher-order
-- abstract syntax, M has to be not a state monad but a continuation monad.

type M = Cont E

runM :: M E -> E
runM m = runCont m id

-- Like on the previous homework, the crucial action in the monad M is to
-- define a new local variable.  Again we call this action "insert_let".

-- 4. (20%) Define "insert_let" below to insert a call to "let_" in the
--    generated code.  This "insert_let" action is used in "powerM" below.
--    For example, "test4" should compute "[True,True]".

insert_let :: E -> M E
insert_let e = cont $ let_ e

powerM :: Int -> E -> M E
powerM 0 _ = return (int 1)
powerM 1 x = return x
powerM n x = let (q,r) = divMod n 2 in
             do y <- insert_let (x `mul` x)
                z <- powerM q y
                return (if r == 0 then z else z `mul` x)

test4 :: [Bool]
test4 = [  runE (lam (\x -> runM (powerM 5 x)))
        == (Lam "x0" $
            Let "x1" (Mul (Var "x0") (Var "x0")) $
            Let "x2" (Mul (Var "x1") (Var "x1")) $
            Mul (Var "x2") (Var "x0"))
        ,   runE (lam (\x -> runM (powerM 10 x)))
        == (Lam "x0" $
            Let "x1" (Mul (Var "x0") (Var "x0")) $
            Let "x2" (Mul (Var "x1") (Var "x1")) $
            Let "x3" (Mul (Var "x2") (Var "x2")) $
            Mul (Var "x3") (Var "x1"))
        ]

-- 5. (20%) The code generator "gibM" below generates way too many
--    multiplications.  For example, "test5'" is huge!  Change "gibM'" to use
--    "insert_let" to generate smaller, more efficient code.  For example,
--    "test5" should compute "True".

gibM :: Int -> E -> E -> M E
gibM 0 a _ = return a
gibM n a b = do (_, result) <- gibM' (n-1) a b
                return result

gibM' :: Int -> E -> E -> M (E, E)
gibM' 0 a b = return (a, b)
gibM' n a b = do (x, y) <- gibM' (n-1) a b
                 z      <- insert_let (x `add` y)
                 return (y, z)

test5 :: Bool
test5 = test5'
        == (Lam "x0" $
            Lam "x1" $
            Let "x2" (Sub (Var "x0") (Sub (Int 0) (Var "x1"))) $
            Let "x3" (Sub (Var "x1") (Sub (Int 0) (Var "x2"))) $
            Let "x4" (Sub (Var "x2") (Sub (Int 0) (Var "x3"))) $
            Let "x5" (Sub (Var "x3") (Sub (Int 0) (Var "x4"))) $
            Let "x6" (Sub (Var "x4") (Sub (Int 0) (Var "x5"))) $
            Let "x7" (Sub (Var "x5") (Sub (Int 0) (Var "x6"))) $
            Let "x8" (Sub (Var "x6") (Sub (Int 0) (Var "x7"))) $
            Let "x9" (Sub (Var "x7") (Sub (Int 0) (Var "x8"))) $
            Let "x10" (Sub (Var "x8") (Sub (Int 0) (Var "x9"))) $
            Var "x10")

test5' :: Term
test5' = runE (lam (\a -> lam (\b -> runM (gibM 10 a b))))