{-# OPTIONS -W #-}
{-
Brandon Burzon (brburzon)
Won Yong Ha (woha)
Simon Lee
-}

module Interp where

import Data.Function (on)

data Term = Int Integer
          | Sub Term Term
          | Less Term Term
          | If Term Term Term
          | Var Name
          | Let Name Term Term
          | Lam Name Term
          | App Term Term
    deriving (Show, Eq)

data Value = N { nOf :: Double }
           | B { bOf :: Bool }
           | F (Value -> Value)
    -- deriving (Show)

instance Show Value where
  show (F _) = "<function>"
  show (N n) = show n
  show (B n) = show n

type Name = String

type Env = [(Name, Value)]

empty :: Env
empty = []

extend :: (Name, Value) -> Env -> Env -- > Wtf
extend n env = n : env

lookUp :: Env -> Name -> Value
lookUp [] _ = error $ "unbound variable"
lookUp (x : xs) name = if name == fst x
                       then snd x
                       else lookUp xs name
-- valueOf :: Term -> Value

valueOf :: Env -> Term -> Value
valueOf _ (Int i)                 = N (fromIntegral i)
valueOf env (Sub x y)             = N (calcValue env (-) x y)
valueOf env (Less x y)            = B (calcValue env (<) x y)
valueOf env (If x y z)            = if bOf (valueOf env x) then valueOf env y else valueOf env z
valueOf env (Var n)               = lookUp env n
valueOf env (Let name value body) = let mvalue = valueOf env value
                                          in valueOf (extend (name , mvalue) env) body
valueOf env (Lam name body) =  F (\value -> (valueOf (extend (name, value) env) body))
valueOf env (App func value) =
  let v1 = valueOf env func
      v2 = valueOf env value
  in case v1 of
    F f -> f v2
    _ -> error $ "not a function"

calcValue :: Env -> (Double -> Double -> a) -> Term -> Term -> a
calcValue env op = on op (nOf . valueOf env)

add :: Term -> Term -> Term
add x y = Sub x (Sub (Int 0) y)

-- new DataType
data ValueD = ND { ndOf :: Double }
            | BD { bdOf :: Bool }
            | FD Term EnvD

instance Show ValueD where
  show (FD term (x:xs)) = show (snd x)
  show (ND n) = show n
  show (BD n) = show n

type EnvD = [(Name, ValueD)]

empty_d :: EnvD
empty_d = []

extend_d :: (Name, ValueD) -> EnvD -> EnvD -- > Wtf
extend_d n env                      = n : env

lookUp_d :: EnvD -> Name -> ValueD
lookUp_d [] _                       = error $ "unbound variable"
lookUp_d (x : xs) name              = if name == fst x
                                      then snd x
                                      else lookUp_d xs name

valueOf_d :: EnvD -> Term -> ValueD
valueOf_d _ (Int i)                 = ND (fromIntegral i)
valueOf_d env (Sub x y)             = ND (calcValueD env (-) x y)
valueOf_d env (Less x y)            = BD (calcValueD env (<) x y)
valueOf_d env (If x y z)            = if bdOf (valueOf_d env x) then valueOf_d env y else valueOf_d env z
valueOf_d env (Var n)               = lookUp_d env n
valueOf_d env (Let name value body) = let rvalue   = valueOf_d env value
                                          in valueOf_d (extend_d (name , rvalue) env) body
valueOf_d env (Lam name body)       = (FD body (extend_d (name , valueOf_d env body) env))
valueOf_d env (App (Lam name body) value)      =
  let FD c env' = valueOf_d env (Lam name body) in
  let v = valueOf_d env value in
  valueOf_d ((name, v) : env') (Lam name c)
valueOf_d env (App (Let name _ _) value2) = valueOf_d env (App (Var name) value2)
valueOf_d _ (App _ _) = error $ "not a function"

calcValueD :: EnvD -> (Double -> Double -> a) -> Term -> Term -> a
calcValueD env op                   = on op (ndOf . valueOf_d env)
-- CPS the interpreter

type Ans                            = ValueC

data ValueC = NC { ncOf :: Double }
            | BC { bcOf :: Bool }
            | FC (ValueC -> ValueC)

instance Show ValueC where
  show (FC _) = "<function>"
  show (NC n) = show n
  show (BC n) = show n

type EnvC = [(Name, ValueC)]

emptyC :: EnvC
emptyC = []

extendC :: (Name, ValueC) -> EnvC -> EnvC -- > Wtf
extendC n env = n : env

lookUpC :: EnvC -> Name -> (ValueC -> ValueC) -> ValueC
lookUpC [] _ k = k $ error $ "unbound variable"
lookUpC (x : xs) name k = if name == fst x
                       then k $ snd x
                       else lookUpC xs name k

valueOf_c :: EnvC -> Term -> (ValueC -> ValueC) -> ValueC
valueOf_c _ (Int i)    k              = k (NC (fromIntegral i))
valueOf_c env (Sub x y)  k              = calcValue_c env (-) x y (\r -> k (NC r))
valueOf_c env (Less x y) k              = calcValue_c env (<) x y (\r -> k (BC r))
valueOf_c env (If x y z) k              = valueOf_c env x (\r -> if bcOf r then valueOf_c env y k
                                                     else valueOf_c env z k)
valueOf_c env (Var n) k             = lookUpC env n k
valueOf_c env (Let name value body) k = let mvalue = valueOf_c env value k
                                          in valueOf_c (extendC (name , mvalue) env) body k
valueOf_c env (Lam name body) k =  FC (\value -> (valueOf_c (extendC (name, value) env) body k))
valueOf_c env (App func value) k =
  let v1 = valueOf_c env func k
      v2 = valueOf_c env value k
  in case v1 of
    FC f -> k (f v2)
    _ -> error $ "not a function"


calcValue_c :: EnvC -> (Double -> Double -> a) -> Term -> Term -> (a -> Ans) -> Ans
calcValue_c env op x y k                = valueOf_c env x $ \r ->
                       valueOf_c env y $ \s ->
                       k (op (ncOf r) (ncOf s))

test1 = valueOf empty (App (Lam "x" (Let "y" (Var "x") (App (Lam "x" (Var "x")) (Int 4))))  (Int 5))
test2 = valueOf_d empty_d (App (Lam "x" (Let "y" (Var "x") (App (Lam "x" (Var "x")) (Int 4))))  (Int 5))
test3 = valueOf_c emptyC (App (Lam "x" (Let "y" (Var "x") (App (Lam "x" (Var "x")) (Int 4))))  (Int 5))  (\y -> y)

{-
What is one difference between what you can do with the interpreters from (1) and (2)?
In the first interpreter, our lambda can accept multiple variables, but the second interpreter can only accept one variable in the lambda.
This is because of Haskell's currying functionality.
-}
