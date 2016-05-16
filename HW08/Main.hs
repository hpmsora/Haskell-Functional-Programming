{-# OPTIONS -W -fno-warn-unused-imports #-}
{-
Brandon Burzon
Simon Lee
Won Yong Ha
Scott Mathews
-}

module Main where

-- Welcome to Homework 8: Transforming and defining monads.
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

import Control.Applicative  (Applicative(..))
import Control.Monad        (liftM, ap)
import Control.Monad.Writer (WriterT, execWriterT, tell, lift)
import qualified Data.Set   as S

-- Many puzzles can be described as a space of states that are connected to each
-- other by transitions (also known as moves).  The goal of the puzzle is often
-- to get from one state to another by making a sequence of transitions.  Monads
-- can be useful for solving such a puzzle because we need to choose transitions
-- and change states.  In fact, we can use monads to solve all such puzzles in
-- one fell swoop.

-- We define a puzzle by a type of states "s", a type of transitions "t", and a
-- function that tells for each state whether it is winning or what transitions
-- from it are available.  In general, to detect cycles among states, we need
-- the type of states "s" to belong to the Ord type class (which has the Eq type
-- class as a superclass), but there is no similar requirement on the type of
-- transitions "t".

data Result s t = Win | Successors [(t,s)] deriving (Show)

type Puzzle s t = s -> Result s t

-- For example, here's a trivial puzzle: Starting at an integer, how do we get
-- to exactly zero, by incrementing or decrementing it?

data IncDec = Inc | Dec deriving (Show)

puzzle1 :: Puzzle Int IncDec
puzzle1 0 = Win
puzzle1 x = Successors [(Inc, x+1), (Dec, x-1)]

-- And here's another trivial puzzle: Starting at an integer, how do we get to
-- exactly zero, by incrementing or decrementing it, modulo 10?

puzzle2 :: Puzzle Int IncDec
puzzle2 0 = Win
puzzle2 x = Successors [(Inc, mod (x+1) 10), (Dec, mod (x-1) 10)]

-- We can use the list monad to solve puzzles.  The idea is that an action in
-- the list monad is to choose a way to proceed.  For example, the list of type
-- "[(t,s)]" in the definition of "Result" above is to choose something of type
-- "(t,s)".  To prune the search, we use a "Set" to keep track of the states we
-- have seen already along the current path, so that we don't consider any path
-- with a cycle in it.

--  1. (10%) Complete the definition of "solve1" below, so "solve1 puzzle2 7"
--     returns a list of two solutions.  In turn, each solution is a list of
--     transition-destination pairs.
--
--      > solve1 puzzle1 1
--      [[(Dec,0)],
--       [(Dec,1),(Dec,0)]]
--
--      > solve1 puzzle2 7
--      [[(Inc,8),(Inc,9),(Inc,0)],
--       [(Dec,6),(Dec,5),(Dec,4),(Dec,3),(Dec,2),(Dec,1),(Dec,0)]]
--
--     The first argument to "solve1" defines the puzzle and the second argument
--     is the start (or current) state.

solve1 :: (Ord s) => Puzzle s t -> s -> [[(t,s)]]
solve1 = solve1' S.empty

solve1' :: (Ord s) => S.Set s -> Puzzle s t -> s -> [[(t,s)]]
solve1' seen p s
  = case (S.member s seen, p s) of
      (True , _             ) -> []
      (False, Win           ) -> return []
      (False, Successors tss) -> tss >>= \ts@(t, s') ->
        solve1' (S.insert s seen) p s' >>= \y -> return (ts:y)


-- We can view the transition-destination pairs produced by solving as a kind of
-- output and incorporate it as part of the action of a monad.  The monad is no
-- longer just the list monad, but with the writer monad transformer applied.

type M s t = WriterT [(t,s)] []

--  2. (20%) Complete the definition of "solve2'" below, so that "solve2"
--     behaves identically to "solve1".

solve2 :: (Ord s) => Puzzle s t -> s -> [[(t,s)]]
solve2 p s = execWriterT (solve2' S.empty p s)

solve2' :: (Ord s) => S.Set s -> Puzzle s t -> s -> WriterT [(t,s)] [] ()
solve2' seen p s
  = case (S.member s seen, p s) of
      (True , _             ) -> lift []
      (False, Win           ) -> return ()
      (False, Successors tss) -> do
        ts@(_,s') <- lift tss
        tell [ts]
        solve2' (S.insert s seen) p s'

-- Let's solve some more interesting puzzles.  Here's a classic, as Wikipedia
-- puts it (https://en.wikipedia.org/wiki/Fox,_goose_and_bag_of_beans_puzzle):
--
--      Once upon a time a farmer went to a market and purchased a fox, a goose,
--      and a bag of beans.  On his way home, the farmer came to the bank of a
--      river and rented a boat.  But in crossing the river by boat, the farmer
--      could carry only himself and a single one of his purchases -- the fox,
--      the goose, or the bag of beans.
--
--      If left together, the fox would eat the goose, or the goose would eat
--      the beans.
--
--      The farmer's challenge was to carry himself and his purchases to the far
--      bank of the river, leaving each purchase intact.  How did he do it?
--
-- Let's represent the states in this puzzle using a "Set" of "Thing"s for each
-- side of the river.  A transition is also a "Set" of "Thing"s, namely the
-- "Thing"s transported, excluding the "Farmer" driving the boat.

data Thing = Farmer | Fox | Goose | Beans | Hunter
  deriving (Eq, Show, Ord)

data State = State { sideA, sideB :: S.Set Thing }
  deriving (Eq, Show, Ord)

startFGB :: State
startFGB = State (S.fromList [Farmer, Fox, Goose, Beans]) S.empty

type Transition = S.Set Thing

--  3. (10%) Complete the definition of "puzzleFGB" below, so that running
--     "solve1 puzzleFGB startFGB" (or "solve2 puzzleFGB startFGB") solves the
--     puzzle and returns two solutions.

puzzleFGB :: Puzzle State Transition
puzzleFGB s
  | S.null (sideA s) = Win
  | any (\side -> not (Farmer `S.member` side s)
               && any (all (`S.member` side s))
                      [[Fox, Goose], [Goose, Beans]])
        [sideA, sideB] = Successors []
  | otherwise = Successors [ (t, s') | t <- [ S.fromList [ Farmer ]
                                             , S.fromList [ Farmer, Fox ]
                                             , S.fromList [ Farmer, Goose ]
                                             , S.fromList [ Farmer, Beans ]
                                             ]
                                      , s' <- let sa = if S.isSubsetOf t (sideA s)
                                                       then S.difference (sideA s) t
                                                       else S.union (sideA s) t
                                                  sb = if S.isSubsetOf t (sideB s)
                                                       then S.difference (sideB s) t
                                                       else S.union (sideB s) t
                                              in [State sa sb]
                                      , S.isSubsetOf t (sideA s) || S.isSubsetOf t (sideB s) ]


-- Similar puzzles abound.  Here's one variation:  The farmer takes his hunter
-- friend along.  She is good company but a bit quick on the trigger.  If the
-- farmer leaves the hunter alone with the fox or the goose, she kills it right
-- away, despite the farmer's wishes.  The boat is still driven by the farmer
-- and holds either the hunter or at most _two_ purchases, besides the farmer.

--  4. (10%) Express the variant puzzle by completing the definitions of
--     "startFGBH" and "puzzleFGBH" below, so that "solve1 puzzleFGBH startFGBH"
--     (or "solve2 puzzleFGBH startFGBH") solves the variant puzzle and returns
--     eight solutions.  Feel free to change the definitions of "Thing" and
--     "puzzleFGB" above, as long as the functionality described in the previous
--     problem remains intact.

startFGBH :: State
startFGBH = State (S.fromList [Farmer, Fox, Goose, Beans, Hunter]) S.empty

puzzleFGBH :: Puzzle State Transition
puzzleFGBH s
  | S.null (sideA s) = Win
  | any (\side -> not (Farmer `S.member` side s)
               && any (all (`S.member` side s))
                      [[Fox, Goose], [Goose, Beans], [Hunter, Fox], [Hunter, Goose]])
        [sideA, sideB] = Successors []
  | otherwise = Successors [ (t, s') | t <- allTransitions
                                     , s' <- let sa = if S.isSubsetOf t (sideA s)
                                                      then S.difference (sideA s) t
                                                      else S.union (sideA s) t
                                                 sb = if S.isSubsetOf t (sideB s)
                                                      then S.difference (sideB s) t
                                                      else S.union (sideB s) t
                                             in [State sa sb]
                                     , S.isSubsetOf t (sideA s) || S.isSubsetOf t (sideB s) ]

allTransitions = S.toList $ S.fromList $ [ S.fromList [ Farmer ]
                 , S.fromList [ Farmer, Fox ]
                 , S.fromList [ Farmer, Goose ]
                 , S.fromList [ Farmer, Beans ]
                 , S.fromList [ Farmer, Hunter ]
                 ] `mappend` [ S.fromList [ x, y, z ] | x <- [Farmer]
                                                      , y <- [Fox, Goose, Beans]
                                                      , z <- [Fox, Goose, Beans]
                                                      , y /= z
                                                      ]

-- It's nice that we can plug different problems into "solve1" and "solve2",
-- but they share the weakness that the search can get stuck in an infinite
-- branch even as a very short path to winning awaits discovery in another
-- branch.  This is a weakness of _depth-first search_ that is addressed by
-- _breadth-first search_.  To implement breadth-first search and find the
-- shortest solutions first, let's define a search tree as a data structure
-- and a monad.  An added benefit of the search tree is that it is easier to
-- understand visually than a list.


exampleTree :: Tree Int String
exampleTree = Branch [(1, Branch [(2, Leaf "world"),
                                  (3, Leaf "!")]),
                      (4, Branch []),
                      (5, Leaf "hello")]
--  5. (10%) Complete the definition of "draw" below so that the tree
--     "exampleTree" is shown as
--
--      |-- 1
--      |   |-- 2
--      |   |   "world"
--      |   `-- 3
--      |       "!"
--      |-- 4
--      `-- 5
--          "hello"
data Tree b a = Leaf a | Branch [(b, Tree b a)]
  deriving (Eq)
instance (Show b, Show a) => Show (Tree b a) where show = unlines . draw

exampleTree1 :: Tree Int String
exampleTree1 = Branch [(1, Leaf "hello")]

{-
draw :: (Show b, Show a) => Tree b a -> [String]
draw (Leaf x) = [show x]
draw (Branch [(9999, x)]) = (myConcat ["    "] (draw x))
draw (Branch [(i, Leaf x)]) = ["|-- " ++ i] ++ (draw (Branch [9999, (Leaf x)]))
draw (Branch [(i, Branch x)]) = ["|-- " ++ i] ++ (draw (Branch [9999, (Branch x)]))
draw (Branch [(i, Leaf x):xs]) = ["|-- " ++ i] ++ (draw (Branch [9999, (Leaf x)])) ++ (draw [9999, xs])
draw (Branch [(i, Branch x):xs]) = ["|-- " ++ i] ++ (draw (Branch [9999, (Branch x)])) ++ (draw [9999, xs])
-}
{-
draw :: (Show b, Show a) => Tree b a -> [String]
draw (Leaf a) 	      	    	     	= [show a]
draw (Branch ((b, Branch x):[]))	= [show ("|-- " ++ "    " ++ b)]
draw (Branch ((b, Leaf x):[]))		= undefined
draw (Branch ((b, Branch (x:xs)):ys))  	= (myConcat "|-- " [show b]) ++ (draw (Branch ((x, Branch xs):[])))
draw (Branch ((b, Leaf x):ys))	   	= undefined
draw (Branch [])       			= undefined
-}
--draw (Leaf a)                    = myConcat ["   "] [show a]
--draw (Branch [])                 = []
--draw (Branch ((b, Leaf a) : [])) = ["`-- " ++ show b] ++ ["    " ++ show a]
--draw (Branch (x:xs))             = ["|-- " ++ show (fst x)] ++ (myConcat (draw (snd x)) (draw (Branch xs)))

-- draw :: Tree String -> [String]
--draw (Branch (bt:bts)) = ["|-- " ++ show (fst bt)] ++ (drawSubTrees bts)
--  where    drawSubTrees [] = []
--           drawSubTrees [t] =        "|" : shift "`-- " "    " (draw (fst t))
--           drawSubTrees (t:ts) =        "|" : shift "+-- " "|   " (draw t) ++ drawSubTrees ts
--           shift first other = zipWith (++) (first : repeat other)

{-
myConcat :: String -> [String] -> [String]
myConcat s [] = [s]
myConcat s (b:bs) = (s ++ b) : bs
-}

draw :: (Show b, Show a) => Tree b a -> [String]
draw (Leaf a)                  = [show a]
draw (Branch [])               = []
draw (Branch (bt:bts))         = ["|-- " ++ show (fst bt)] ++ shift "|   " "|   " (draw (snd bt)) ++ (drawSubTrees bts)
  where    drawSubTrees []     = []
           drawSubTrees [t]    = shift "`-- " "|   " [(show (fst t))] ++ shift "    " "    " (draw (snd t))
           drawSubTrees ((a, Branch []):ts) =  shift "|-- " "|   " [(show a)] ++ drawSubTrees ts
           drawSubTrees (t:ts) = shift "|-- " "|   " ([(show (fst t))] ++ (draw (snd t)) ++ drawSubTrees ts)
           shift first other   = zipWith (++) (first : repeat other)


-- checkIfEmpty (Branch x) = if x == []
--                  then [""]
--                  else (myConcat ["|   "] (draw x))

main :: IO ()
main = putStrLn (show exampleTree)

--  6. (20%) Complete the Monad instance below to make "solve" work.  For
--     example, "solve puzzle2 7" should return the tree
--
--      |-- (Inc,8)
--      |   |-- (Inc,9)
--      |   |   |-- (Inc,0)
--      |   |   |   ()
--      |   |   `-- (Dec,8)
--      |   `-- (Dec,7)
--      `-- (Dec,6)
--          |-- (Inc,7)
--          `-- (Dec,5)
--              |-- (Inc,6)
--              `-- (Dec,4)
--                  |-- (Inc,5)
--                  `-- (Dec,3)
--                      |-- (Inc,4)
--                      `-- (Dec,2)
--                          |-- (Inc,3)
--                          `-- (Dec,1)
--                              |-- (Inc,2)
--                              `-- (Dec,0)
--                                  ()
--
--     and "solve puzzleFGB startFGB" should return the tree
--
--      |-- (fromList [Fox],State {sideA = fromList [Goose,Beans], sideB = fromList [Farmer,Fox]})
--      |-- (fromList [Goose],State {sideA = fromList [Fox,Beans], sideB = fromList [Farmer,Goose]})
--      |   |-- (fromList [Goose],State {sideA = fromList [Farmer,Fox,Goose,Beans], sideB = fromList []})
--      |   `-- (fromList [],State {sideA = fromList [Farmer,Fox,Beans], sideB = fromList [Goose]})
--      |       |-- (fromList [Fox],State {sideA = fromList [Beans], sideB = fromList [Farmer,Fox,Goose]})
--      |       |   |-- (fromList [Fox],State {sideA = fromList [Farmer,Fox,Beans], sideB = fromList [Goose]})
--      |       |   |-- (fromList [Goose],State {sideA = fromList [Farmer,Goose,Beans], sideB = fromList [Fox]})
--      |       |   |   |-- (fromList [Goose],State {sideA = fromList [Beans], sideB = fromList [Farmer,Fox,Goose]})
--      |       |   |   |-- (fromList [Beans],State {sideA = fromList [Goose], sideB = fromList [Farmer,Fox,Beans]})
--      |       |   |   |   |-- (fromList [Fox],State {sideA = fromList [Farmer,Fox,Goose], sideB = fromList [Beans]})
--      |       |   |   |   |   |-- (fromList [Fox],State {sideA = fromList [Goose], sideB = fromList [Farmer,Fox,Beans]})
--      |       |   |   |   |   |-- (fromList [Goose],State {sideA = fromList [Fox], sideB = fromList [Farmer,Goose,Beans]})
--      |       |   |   |   |   |   |-- (fromList [Goose],State {sideA = fromList [Farmer,Fox,Goose], sideB = fromList [Beans]})
--      |       |   |   |   |   |   |-- (fromList [Beans],State {sideA = fromList [Farmer,Fox,Beans], sideB = fromList [Goose]})
--      |       |   |   |   |   |   `-- (fromList [],State {sideA = fromList [Farmer,Fox], sideB = fromList [Goose,Beans]})
--      |       |   |   |   |   `-- (fromList [],State {sideA = fromList [Fox,Goose], sideB = fromList [Farmer,Beans]})
--      |       |   |   |   |-- (fromList [Beans],State {sideA = fromList [Farmer,Goose,Beans], sideB = fromList [Fox]})
--      |       |   |   |   `-- (fromList [],State {sideA = fromList [Farmer,Goose], sideB = fromList [Fox,Beans]})
--      |       |   |   |       |-- (fromList [Goose],State {sideA = fromList [], sideB = fromList [Farmer,Fox,Goose,Beans]})
--      |       |   |   |       |   ()
--      |       |   |   |       `-- (fromList [],State {sideA = fromList [Goose], sideB = fromList [Farmer,Fox,Beans]})
--      |       |   |   `-- (fromList [],State {sideA = fromList [Goose,Beans], sideB = fromList [Farmer,Fox]})
--      |       |   `-- (fromList [],State {sideA = fromList [Farmer,Beans], sideB = fromList [Fox,Goose]})
--      |       |-- (fromList [Beans],State {sideA = fromList [Fox], sideB = fromList [Farmer,Goose,Beans]})
--      |       |   |-- (fromList [Goose],State {sideA = fromList [Farmer,Fox,Goose], sideB = fromList [Beans]})
--      |       |   |   |-- (fromList [Fox],State {sideA = fromList [Goose], sideB = fromList [Farmer,Fox,Beans]})
--      |       |   |   |   |-- (fromList [Fox],State {sideA = fromList [Farmer,Fox,Goose], sideB = fromList [Beans]})
--      |       |   |   |   |-- (fromList [Beans],State {sideA = fromList [Farmer,Goose,Beans], sideB = fromList [Fox]})
--      |       |   |   |   |   |-- (fromList [Goose],State {sideA = fromList [Beans], sideB = fromList [Farmer,Fox,Goose]})
--      |       |   |   |   |   |   |-- (fromList [Fox],State {sideA = fromList [Farmer,Fox,Beans], sideB = fromList [Goose]})
--      |       |   |   |   |   |   |-- (fromList [Goose],State {sideA = fromList [Farmer,Goose,Beans], sideB = fromList [Fox]})
--      |       |   |   |   |   |   `-- (fromList [],State {sideA = fromList [Farmer,Beans], sideB = fromList [Fox,Goose]})
--      |       |   |   |   |   |-- (fromList [Beans],State {sideA = fromList [Goose], sideB = fromList [Farmer,Fox,Beans]})
--      |       |   |   |   |   `-- (fromList [],State {sideA = fromList [Goose,Beans], sideB = fromList [Farmer,Fox]})
--      |       |   |   |   `-- (fromList [],State {sideA = fromList [Farmer,Goose], sideB = fromList [Fox,Beans]})
--      |       |   |   |       |-- (fromList [Goose],State {sideA = fromList [], sideB = fromList [Farmer,Fox,Goose,Beans]})
--      |       |   |   |       |   ()
--      |       |   |   |       `-- (fromList [],State {sideA = fromList [Goose], sideB = fromList [Farmer,Fox,Beans]})
--      |       |   |   |-- (fromList [Goose],State {sideA = fromList [Fox], sideB = fromList [Farmer,Goose,Beans]})
--      |       |   |   `-- (fromList [],State {sideA = fromList [Fox,Goose], sideB = fromList [Farmer,Beans]})
--      |       |   |-- (fromList [Beans],State {sideA = fromList [Farmer,Fox,Beans], sideB = fromList [Goose]})
--      |       |   `-- (fromList [],State {sideA = fromList [Farmer,Fox], sideB = fromList [Goose,Beans]})
--      |       `-- (fromList [],State {sideA = fromList [Fox,Beans], sideB = fromList [Farmer,Goose]})
--      |-- (fromList [Beans],State {sideA = fromList [Fox,Goose], sideB = fromList [Farmer,Beans]})
--      `-- (fromList [],State {sideA = fromList [Fox,Goose,Beans], sideB = fromList [Farmer]})
--
--     with the subtrees possibly permuted at each Branch.

instance Functor (Tree b) where
  fmap  = liftM

instance Applicative (Tree b) where
  pure  = return
  (<*>) = ap

instance Monad (Tree b) where
  return a = Leaf a
  (>>=) (Leaf a) f = f a
  (>>=) (Branch bts) f = Branch (map (\bt -> (fst bt, snd bt >>= f)) bts)

-- data Tree b a = Leaf a | Branch [(b, Tree b a)]
--   deriving (Eq)

solve :: (Ord s) => Puzzle s t -> s -> Tree (t,s) ()
solve = solve' S.empty

solve' :: (Ord s) => S.Set s -> Puzzle s t -> s -> Tree (t,s) ()
solve' seen p s
  = case (S.member s seen, p s) of
      (True , _             ) -> Branch []
      (False, Win           ) -> return ()
      (False, Successors tss) -> do
        s' <- Branch [ (ts, return s') | ts@(_,s') <- tss ]
        solve' (S.insert s seen) p s'

-- The following function traverses a Tree and returns its Leaf nodes in
-- breadth-first order.  For example, "bfs exampleTree" returns the list
--
--      ["hello","world","!"]

bfs :: Tree b a -> [a]
bfs t = bfs' [t]
  where
    bfs' [] = []
    bfs' ts = let (top, below) = unzip (map f ts)
              in concat top ++ bfs' (concat below)
    f (Leaf a)     = ([a], [])
    f (Branch bts) = ([] , map snd bts)

-- But we want to see the path to each leaf, not just the leaf itself.

--  7. (10%) Complete the definition of "labelPaths" below, to pair each Leaf
--     value with the list of Branch labels leading to that Leaf.  For example,
--     "labelPaths exampleTree" should return the tree
--
--      |-- 1
--      |   |-- 2
--      |   |   ([1,2],"world")
--      |   `-- 3
--      |       ([1,3],"!")
--      |-- 4
--      `-- 5
--          ([5],"hello")

labelPaths :: Tree b a -> Tree b ([b],a)
labelPaths (Leaf a)     = Leaf ([],a)
labelPaths (Branch bts) = undefined

--  8. (10%) Now we can solve all our puzzles and return the shortest solution
--     paths first!  Do so by putting the building blocks above together and
--     completing the definition of "solveBfs" below.  In particular, calling
--     "head (solveBfs puzzle1 7)" should return
--
--      [(Dec,6),(Dec,5),(Dec,4),(Dec,3),(Dec,2),(Dec,1),(Dec,0)]

solveBfs :: (Ord s) => Puzzle s t -> s -> [[(t,s)]]
solveBfs p s = undefined $ solve p s
