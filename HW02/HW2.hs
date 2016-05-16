
module HW2 where

{-

Here is the definition for the type of natural numbers, in what is known as Peano representation.
A natural number is either zero, or it is the successor of another natural number.

-}

data Nat
  = Zero
  | Suc Nat
  deriving (Show)

-- Section 1 (10%) -------------------------------------------------------------

-- nat is a convenient function that takes an Int to its Nat representation.
-- for example:
--  nat 0 = Zero
--  nat 2 = Suc (Suc Zero)
nat :: Int -> Nat
nat n =
  if n <= 0
  then Zero
  else Suc (nat (pred n))

{-

1. Fill in the definition of `int`, which takes a Nat back
   to an Int.

     int Zero                 = 0
     int (Suc (Suc Zero))     = 2
     int (Suc (Suc (Suc Zero) = 3



int :: Nat -> Int
int Zero = 0
int (Suc n) = 1 + int n
-}

-- Section 2 (60%) -------------------------------------------------------------
{-
-- add two natural numbers together.
add :: Nat -> Nat -> Nat
add Zero    y = y
add (Suc x) y = Suc (add x y)

-- multiply two natural numbers.
mul :: Nat -> Nat -> Nat
mul Zero    y = Zero
mul (Suc x) y = add (mul x y) y

-- pow raises its first argument to the power of the second argument.
-- for example:
--   int (pow (nat 2) (nat 2)) = 4
--   int (pow (nat 3) (nat 2)) = 9
pow :: Nat -> Nat -> Nat
pow x Zero    = Suc Zero
pow x (Suc y) = mul (pow x y) x


2. Fill in the definition of `foldNat`, and
-}

foldNat :: a -> (a -> a) -> Nat -> a
foldNat x _ (Zero) = x
foldNat x f (Suc n) = f (foldNat x f n)

{-
3-6. Rewrite `int`, `add`, `mul`, and `pow`
     to use `foldNat` instead of explicit
     recursion over its argument.
-}
--3.

int :: Nat -> Int
int Zero = 0
int n = foldNat 0 (+ 1) n

--4.

add :: Nat -> Nat -> Nat
add Zero y = y
add (Suc x) y = Suc (foldNat x Suc y)

--5.

mul :: Nat -> Nat -> Nat
mul Zero y = Zero
mul (Suc x) y = (foldNat y (add y) x)

--6.

pow :: Nat -> Nat -> Nat
pow x Zero = Suc Zero
pow x (Suc y) = (foldNat x (mul x) y)

{-
-- factorial of a number: fact x = x * (x-1) * (x-2) * ... * 1
fact :: Nat -> Nat
fact x = case x of
  Zero  -> Suc Zero
  Suc y -> mul (fact y) x
-}
{-

6. Is it possible to redefine `fact` with `foldNat`?

No

7. If so, write a definition for `fact` that uses `foldNat`
     instead of explicit recursion.
   If not, explain why `fact` cannot be defined with `foldNat`,
     and what changes to `foldNat` would need to be made in
     order to do so.

The reason function 'fact' made by 'foldNat' is not possible would be the
function 'foldNat' only can handle fixed variable which mean the fix variable
is only possible to use procedure of the foldNat. So if foldNat accepts second
function variable like 'add n1 n2' or 'pow n1 n2', it will be possible. 
Like upon said if the foldNat can change the returning variable, it will be
possible. In this fact function, subtraction function will be needed.
-})


-- Section 3 (30%) -------------------------------------------------------------

{-

From arithmetic, we know that when adding three numbers together,
we get the same result whether we first add the first two and then
add the third to the result, or if we first add the last two numbers,
and then add the first to the result. This is known as *associativity*.

For our `add` function, this gives us the following equation:

    add x (add y z) = add (add x y) z

  We'll call this rule 'add-assoc'.

(For some fun, try proving this using the definition of `add`!)

-}

foldLeft :: b -> (b -> a -> b) -> [a] -> b
foldLeft b f []       = b
foldLeft b f (a : as) = foldLeft (f b a) f as

foldRight :: b -> (a -> b -> b) -> [a] -> b
foldRight b f []       = b
foldRight b f (a : as) = f a (foldRight b f as)

sumLeft :: [Nat] -> Nat
sumLeft = foldLeft Zero add

sumRight :: [Nat] -> Nat
sumRight = foldRight Zero add

{-

8. Use beta and add-assoc steps to show that, for any xs :: [Nat],

     sumLeft xs = sumRight xs
     
     1) Base case ([])
     sumLeft [] = sumRight []
     
     LHS
     = sumLeft []
     = foldLeft Zero add []			by 1st def of sumLeft
     = Zero	     	 			by 1st def of foldLeft

     RHS
     = sumRgight []
     = foldRighth Zero add []			by 1st def of sumRight
     = Zero	       	   			by 1st def of foldRight
     = LHS

     2) non-Base case (x:xs)
     sumLeft [x:xs] = sumRight [x:xs]
     IH = sumLeft xs = sumRight xs
     	= foldLeft Zero add xs = foldRight Zero add xs
     
     sumLeft (x:xs)
     = foldLeft Zero add (x:xs)			by 1st def of sumLeft
     = foldLeft (add Zero x) add xs		by 2nd def of foldLeft
     = foldLeft x add xs     	 		by def of add

     sumRight (x:xs)  				by 1st def of sumLeft
     = add x (foldRight Zero add xs)		by 2nd def of foldRight
     = add x (foldLeft Zero add xs)		by IH
     = foldLeft (add x Zero) add xs		by mu
     = foldLeft x add xs
     = LHS

     mu:

     add x (foldLeft Zero add xs) = foldLeft (add Zero x) add xs

     mu.1) Base case []
     add x (foldLeft Zero add []) = foldLeft (add Zero x) add []

     LHS
     = add x (foldLeft Zero add [])
     = add x Zero				by 1st def of foldLeft
     = x     					by def of add

     RHS
     = foldLeft (add Zero x) add []
     = foldLeft x add []			by def of add
     = x	      				by 1st def of foldLeft
     = LHS

     mu.2) non-Base case (x:xs)
     add x (foldLeft Zero add (x:xs)) = foldLeft (add Zero x) add (x:xs)
     IH = add x (foldLeft Zero add xs) = foldLeft (add Zero x) add xs
     	= add x (foldLeft Zero add xs) = foldLeft x add xs
     
     LHS
     = add x (foldLeft Zero add (x:xs))
     = add x (foldLeft (add Zero x) add xs)	by 2nd def of foldLeft
     = add x (foldLeft x add xs)    		by def of add
     = foldLeft (add x x) add xs	 	by IH

     RHS
     = foldLeft (add Zero x) add (x:xs)
     = foldLeft x add (x:xs)			by def of add
     = foldLeft (add x x) add xs		by 2nd def of foldLeft
     = LHS


9. Which of the two functions, `sumLeft` and `sumRight`, is more efficient, and why?

   foldRight
   
   Simply saying, the reason is function 'add'.

   For example, let variable VAR had many  Nat variable call V1 V2 V3 ..
   Vn-1 Vn so on, and each variable had various length, can be Zero or 
   all same.

   Then the VAR has been inserted the function sumLeft and sumRight.

   The sumLeft and sumRight would be

   sumLeft [V1 V2 V3 .. Vn-1 Vn]
   and
   sumRight [V1 V2 V3 .. Vn-1 Vn]

   sumLeft [V1 V2 V3 .. Vn-1 Vn]
   = foldLeft Zero add [V1 V2 V3 .. Vn-1 Vn]
   = foldLeft (add Zero V1) add [V2 V3 .. Vn-1 Vn]
   = foldLeft (add (add Zero V1) V2) add [V3 V4 .. Vn-1 Vn]
   ...
   = add (add ... (add Zero V1) V2) ... Vn-1) Vn

   sumRight [V1 V2 V3 .. Vn-1 Vn]
   = foldRight Zero add [V1 V2 V3 .. Vn-1 Vn]
   = add V1 (foldRight Zero add [V2 V3 .. Vn-1 Vn])
   = add V1 (add V2 (fold Zero add [V3 V4 .. Vn-1 Vn]))
   ...
   = add V1 (add V2 (add V3 ... (add Vn-1 Vn)) .. )

   Because the function 'add' is
   
   add :: Nat -> Nat -> Nat
   add Zero y 	 = y
   add (Suc x) y = Suc (add x y)

   , the steps of the function is depend on the first adding variable,
   which mean, if 

   add Var1 Var2

   , the efficiency of the add function would be depend on Var1. If the
   Var1 is longer than Var2, the efficiency is low. Opposite way, if the
   Var2 is longer than Var1, the efficiency is high.

   So,

   sumLeft [V1 V2 V3 .. Vn-1 Vn]'s first adding variables are,

   Zero, V1, V1 + V2, V1 + V2 + V3, ... Vn-2 + Vn-1 + Vn

   But,

   SumRight [V1 V2 V3 .. Vn-1 Vn]'s first adding variables are,

   Vn, Vn-1,  Vn-2, .. V3, V2, V1

   For comparasion, if we add all those first adding variable together,

   sumLeft [V1 V2 V3 .. Vn-1 Vn]
   -> V1 + V2 * 2 + V3 * 3 + ... + Vn * n

   and

   sumRight [V1 V2 V3 .. Vn-1 Vn]
   -> V1 + V2 + V3 ... Vn-1 + Vn

   So, because the all V's length is more than equal to Zero,

   V1 + V2 + V3 ... Vn-1 + Vn >= V1 + V2 * 2 + .. + Vn * n

   Therefore,

   sumRight is more efficience than sumLeft

-}



main = int Zero