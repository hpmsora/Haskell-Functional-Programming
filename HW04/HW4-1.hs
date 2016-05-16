--Won Yong Ha (woha)
--Feb 6 2016
--HW4
--Collaboration:	Brandon Burzon (brburzon)
--			Simon Lee (sijlee)

{-# OPTIONS -W #-}

module HW4 where

-- Welcome to Homework 4: Algebraic Data Types.
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

-- Section 1 (20%) -------------------------------------------------------------

-- The code below defines the types "Point" and "Shape" and some handy
-- functions:

data Point = MkPoint { x, y :: Double }
  deriving (Eq, Show)

translatePoint :: Double -> Double -> Point -> Point
translatePoint dx dy (MkPoint x1 y1)
  = MkPoint (dx + x1)
            (dy + y1)

scalePointFrom :: Double -> Point -> Point -> Point
scalePointFrom s (MkPoint x0 y0)
                 (MkPoint x1 y1)
  = MkPoint (x0 + s * (x1 - x0))
            (y0 + s * (y1 - y0))

data Shape = Circle    Point Double -- radius is non-negative
           | Rectangle Point Point  -- two corners
           | Group     [Shape]
  deriving (Eq, Show)

mass :: Shape -> Double
mass (Circle _ r)
  = 2 * pi * r
mass (Rectangle (MkPoint x1 y1) (MkPoint x2 y2))
  = 2 * (abs (x1 - x2) + abs (y1 - y2))
mass (Group shs)
  = sum (map mass shs)

-- 1. Finish the definition of the "translate" function below.

translate :: Double -> Double -> Shape -> Shape
translate dx dy (Circle pt r)
  = Circle (translatePoint dx dy pt) r
translate dx dy (Rectangle pt1 pt2)
  = Rectangle (translatePoint dx dy pt1) (translatePoint dx dy pt2)
translate dx dy (Group x)
  = Group (map (\xs -> (translate dx dy xs)) x)

-- 2. Finish the definition of the "scaleFrom" function below.

scaleFrom :: Double -> Point -> Shape -> Shape
scaleFrom s pt0 (Circle pt r)
  = Circle (scalePointFrom s pt0 pt) (s * r)
scaleFrom s pt0 (Rectangle p1 p2)
  = Rectangle (scalePointFrom s pt0 p1) (scalePointFrom s pt0 p2)
scaleFrom s pt0 (Group x)
  = Group $ map (\xs -> (scaleFrom s pt0 xs)) x

--Testing
--test1 = translate 5 5 (Circle (MkPoint 4 4) 2)
--test2 = scaleFrom 5 (MkPoint 2 0) (Circle (MkPoint 2 2) 3)

-- Section 2 (20%) -------------------------------------------------------------

-- 3. (Thanks to Mitchell Wand for this problem.)
--    A coffee machine has two items: coffee and hot chocolate.

data Item = Coffee | HotChocolate
  deriving (Eq, Ord, Show)

--    Coffee is $1.50, but hot chocolate is $0.60. A customer may put any
--    sequence of coins into the machine, and then select an item. If the
--    customer has deposited enough money into the machine, and the machine is
--    not out of the selected item, then the machine will dispense the requested
--    item. If the machine is out of the selected item, the machine will flash
--    "Out of Item". The customer may also press "change", in which case the
--    machine will return any unspent money that the customer has put in during
--    the current transaction. If none of these apply, the machine does nothing.
--
--    For example, the customer may put three 25-cent pieces into the machine.
--    If they then select the hot chocolate, the machine will dispense a cup
--    of hot chocolate. If they try to select the coffee instead, nothing will
--    happen. If the customer then presses "change", the machine will return the
--    extra $0.15 that they are owed. The customer may request "change" at any
--    time, whether or not they have ordered anything, and we assume that the
--    machine can always make the required amount of change.
--
--    The machine has a container, called the bank, that contains all the money
--    it has kept from customers' purchases. The customer's money is added to
--    the bank only after they have successfully made a purchase.
--
--    The possible inputs from the customer and outputs from the machine are
--    given by the following data definitions:

data CustomerInput
  = Deposit Integer     -- insert the specified _positive_ amount of money,
                        -- in cents
  | Request Item        -- request an Item
  | Change              -- return all the unspent money that the customer
                        -- has inserted
  deriving (Eq, Show)

data MachineOutput
  = Dispense Item       -- machine dispenses an Item
  | OutOfItem           -- machine displays "Out of Item"
  | Return Integer      -- machine releases the specified _positive_ amount
                        -- of money, in cents
  deriving (Eq, Show)

--    You are to define a type MachineState and the following functions:

initial :: Integer      -- a non-negative number of cups of coffee
        -> Integer      -- a non-negative number of cups of hot chocolate
        -> MachineState -- the state of a machine loaded with the given number
                        -- of cups of coffee and of hot chocolate, with an
                        -- empty bank
initial  cupCoffee cupOfHotChocolate = State cupCoffee cupOfHotChocolate 0 0

transition :: MachineState          -- a machine state
           -> CustomerInput         -- a customer input
           -> (Maybe MachineOutput, -- the machine's response
               MachineState)        -- the MachineState that should follow
transition (State coffee chocolate bank change) (Deposit int) 
	   = (Nothing, (State coffee chocolate bank (change + int)))
transition (State coffee chocolate bank change) (Request Coffee)
	   = if change >= 150
	   then if coffee >= 1
	   	then (Just (Dispense Coffee), (State (coffee - 1) chocolate (bank + 150) (change - 150)))
		else (Just OutOfItem, (State coffee chocolate bank change))
	   else (Nothing, (State coffee chocolate bank change))
transition (State coffee chocolate bank change) (Request HotChocolate)
	   = if change >= 60
	   then if chocolate >= 1
	   	then (Just (Dispense HotChocolate), (State coffee (chocolate - 1) (bank - 60) (change- 60)))
		else (Just OutOfItem, (State coffee chocolate bank change))
	   else (Nothing, (State coffee chocolate bank change))
transition (State coffee chocolate bank change) Change
	   = (Just (Return change), (State coffee chocolate bank 0))

machineBank
  :: MachineState
  -> Integer    -- the amount of money in the machine's bank, in cents
machineBank (State _ _ bank _) = bank

machineRemainingCoffee
  :: MachineState
  -> Integer    -- the number of cups of coffee left in the machine
machineRemainingCoffee (State coffee _ _ _) = coffee

machineRemainingHotChocolate
  :: MachineState
  -> Integer    -- the number of cups of hot chocolate left in the machine
machineRemainingHotChocolate (State _ chocolate _ _) = chocolate

data MachineState 
     = State {coffee, chocolate, bank, change :: Integer}
     deriving (Eq, Show)

-- Section 3 (60%) -------------------------------------------------------------

-- The code below defines "main1" in terms of "concatMap1":

concatMap1 :: (Int -> String) -> [Int] -> String
concatMap1 _ []     = []
concatMap1 f (x:xs) = f x ++ concatMap1 f xs

main1 :: String
main1 = concatMap1 (\x -> concatMap1 (inner x) [1..9]) [1..9]
  where inner x y = show x ++ " times " ++ show y ++
                    " is " ++ show (x * y) ++ ".\n"

-- 4. Turn concatMap1 and main1 into CPS (so that main1 == main1_c),
--    without turning the other functions used such as (++) into CPS. (15%)

--concatMap1_c :: (Int -> (String -> ans) -> ans) -> [Int] -> (String -> ans) -> ans
concatMap1_c :: (Int -> String) -> [Int] -> (String -> ans) -> ans
concatMap1_c fn [] k = k []
concatMap1_c fn (x:xs) k = concatMap1_c fn xs (\v -> (k ((fn x) ++ v)))

main1_c :: String
main1_c = concatMap1_c (\x -> concatMap1_c (inner x) [1..9] emptyK) [1..9] emptyK
	where inner x y = show x ++ " times " ++ show y ++ " is " ++ show(x * y) ++ ".\n"

emptyK = \v -> v


-- 5. Defunctionalize concatMap1 and main1 (so that main1 == main1_d). (15%)

concatMap1_d :: Fun1 -> [Int] -> String
concatMap1_d _ [] = applyFun1 Empty 0
concatMap1_d fun (x:xs) = (applyFun1 fun x) ++ concatMap1_d fun xs

main1_d :: String
main1_d = concatMap1_d (App (\x -> concatMap1_d (App (inner x)) [1..9])) [1..9]
  where inner x y = show x ++ " times " ++ show y ++
                    " is " ++ show (x * y) ++ ".\n"

data Fun1 = Empty | App (Int -> String)
  -- deriving (Eq, Show)

applyFun1 :: Fun1 -> Int -> String
applyFun1 Empty _ = ""
applyFun1 (App fun) i = fun i

test5 = concatMap1_d (App show) [1,2,3,4,5]


-- 6. Defunctionalize concatMap1_c and main1_c (so that main1_c == main1_cd),
--    while specializing the type variable "ans" to the type "String". (15%)

type Ans = String

concatMap1_cd :: Fun1C -> [Int] -> Cont1 -> Ans
concatMap1_cd _ [] cont = applyFun1C Emptyc 0 cont
concatMap1_cd fun (x:xs) cont = (applyFun1C fun x cont) ++ concatMap1_cd fun xs cont

main1_cd :: String
main1_cd = concatMap1_cd (Appc (\x -> concatMap1_cd (Appc (inner x)) [1..9] Emptyk)) [1..9] Emptyk
  where inner x y = show x ++ " times " ++ show y ++" is " ++ show (x * y) ++ ".\n"

data Fun1C = Emptyc | Appc (Int -> Ans)
--deriving (Eq, Show)

data Cont1 = Emptyk | Cont (String -> Ans)
--deriving (Eq, Show)

applyFun1C :: Fun1C -> Int -> Cont1 -> Ans
applyFun1C Emptyc _ cont = applyCont1 cont ""
applyFun1C (Appc fun) i (Cont k) = applyCont1 (Cont k) (fun i)
applyFun1C (Appc fun) i Emptyk = applyCont1 Emptyk (fun i)

applyCont1 :: Cont1 -> String -> Ans
applyCont1 Emptyk v = v
applyCont1 (Cont f) v = f v 

test6 = concatMap1_cd (Appc show) [1, 2, 3, 4, 5, 6] Emptyk

--FUNC1 !!

-- 7. Turn concatMap1_cd, main1_cd, applyFun1C, and applyCont1 into a state
--    machine, so that main1_cd == head [ r | Done r <- iterate go Main1_cd ]
--    (15%)
{-
data State = Done String | Head State
--deriving (Eq, Show)

go :: State -> State
go (Done str) = 
-}