2026-05-25
==========

Write a Haskell program that computes highscores for the following solo-player game.

Consider binary trees with some operations:
```haskell
data Tree
  = Leaf
  | Node Tree Tree
  deriving (Eq, Ord, Show)

concat :: Tree -> Tree -> Tree
concat = Node

rotate :: Tree -> Maybe Tree
rotate (Node (Node t1 t2) t3) = Just (Node t1 (Node t2 t3))
rotate _ = Nothing

tail :: Tree -> Maybe Tree
tail (Node Leaf t) = Just t
tail _ = Nothing
```
A game starts with `n` leaves:
```haskell
type Board = [Tree]     -- Actually use a newtype here to get a hash function derived!

start :: Int -> Board
start n = replicate n Leaf
```
At each turn the player can pick one of the following moves:
```haskell
type Index = Int

data Move
  = Concat Index Index  -- ^ Pretty-printed as @i&j@ where @i, j >=0@ are the indices.
  | Rotate Index        -- ^ Pretty-printed as @ri@ where @i >= 0@ is index.
  | Tail Index          -- ^ Pretty-printed as @ti@ where @i >= 0@ is index.
```
The moves are subject to preconditions as implicit in the following code:
```haskell
move :: Move -> Board -> Maybe Board
move = \case
  Concat i1 i2 -> moveConcat i1 i2
  Rotate i -> moveRotate i
  Tail i   -> moveTail i

-- | Take out a left and a right subtree and insert the concatenation into the tree list.
moveConcat :: Index -> Index -> Board -> Maybe Board
moveConcat i1 i2 b = do
  (t1, b1) <- takeOut i1 b
  (t2, b2) <- takeOut i2 b1
  Just $ insert (Node t1 t2) b2

-- | Take tree at given index and rotate, and insert back.
moveRotate :: Index -> Board -> Maybe Board
moveRotate i b = do
  (t1, b1) <- takeOut i b
  t <- rotate t1
  Just $ insert t b1

-- | Take tail of tree at given index, and insert back.
moveTail :: Index -> Board -> Maybe Board
moveTail i b = do
  (t1, b1) <- takeOut i b
  t <- tail t1
  Just $ insert t b1

-- | Take tree at given index.
takeOut :: Index -> Board -> Maybe (Tree, Board)
takeOut 0 (t : ts) = Just (t, ts)
takeOut n (t : ts) | n >= 0 = second (t:) <$> takeOut (n-1) ts
takeOut _ _ = Nothing

-- | Insert tree into sorted list.
insert :: Tree -> Board -> Board
insert t [] = [t]
insert t (t' : ts)
  | t <= t' -> t : t' : ts
  | otherwise -> t' : insert t ts
```
The goal of the game is, from a given start position, to make the maximum number of rotation moves, while other moves (concat and tail) do not enter the score, but may help to get a higher score eventually.

The goal the program is, for each start position N=0,1,2,3, print the highscore (maximum number of rotations) and the space-separated list of moves leading to this highscore, and the quotient of the highscore by N up to 2 decimal digits precision.

The unexplored positions of the game tree shall be stored as a hashmap mapping `Board` to supplementary position information, which is the list of moves leading to this position and the score (number of rotation moves in this list).
At each iteration, one of the unexplored positions is taken out of the hashmap and replaced by all possible successor positions according to the moves possible from this position.  When a newly entering position has the same Board as a position already existing in the hashmap, the one with a higher score shall be kept.

There is also a `winner` component of the game state, which is `Nothing` in the beginning and in the end shall contain the highscore and the move list leading to the highscore.

The terminal position of the game is the board `[Leaf]` which does not permit any moves.  Whenever this position is reached, its score is compared to the current winner and when it better it replaces the current winner.
Each time a better highscore is reached, the current leader shall be printed (score, quotient, move list) unless an option `--quiet` (short `-q`) is passed at the command line.
The final winner is printed always, and also appended to CSV file `score.csv` (or whatever the user passes with flag `--output` (short `-o`)).

Once the winner of game N is determined, game N+1 is started.  To exit the program, the user just sends the interrupt signal (pressing Ctrl-C), so effectively, it is an infinite loop.


Style guide:
------------

- Use type synonyms with telling names instead of just `Int` etc.
- Use hand-rolled datatypes instead of tuples, `Either`, `Maybe` combinations when defining meaningful structures.
- Comment each data type with a purpose statement, and each of its constructors,, and also the fields where the purpose is unclear.
- Comment each function with a purpose statement and document pre- and postconditions (if any).
- Use Haddock-style comments where possible.
- In longer functions, document each logical step with inline comments.
- Use `optparse-applicative` for option declaration and parsing, and include a `--help` option.


Answer (Copilot)
================

Implemented a standalone Cabal executable in app/Main.hs with package config in
sattler-puzzle.cabal. It uses a Board newtype with Hashable, keeps unexplored positions in a
HashMap, tracks the best-known score per board for pruning, prints improving leaders unless
--quiet is set, always prints the final winner, appends CSV rows via --output, and loops over
N = 0, 1, 2, ... until interrupted.

--help is wired through optparse-applicative, and the early games come out as expected,
including:

 - N=0 score=0 ratio=n/a
 - N=1 score=0 ratio=0.00
 - N=2 score=0 ratio=0.00
 - N=3 score=1 ratio=0.33

I treated the N=0 ratio as n/a to avoid dividing by zero.
