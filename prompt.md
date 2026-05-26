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

2026-05-25 II
=============

Make the following changes:
- start with N=3
- make `--quiet` the default (no leader printing) and add an option `--verbose` (leader printing)
- Remove the following data types and use tuples (and preferably matching on tuples rather than projections) instead:
  RemovedTree, FrontierEntry, FrontierPop, SuccessorPosition.
- record the number of iterations (calls to searchLoop) and print them before the move list (output and csv file)
- add an option to start with a certain N: `--start=N`
- add an option (`--plot`) that reads the CSV file and prints a SVG plot that has on the x axis N and on the y axis the high-score
- organize the project into several modules:
  * one for just the `Tree` and the operations on trees
  * one for the game logic: `Board`, `Move`, valid moves, performing moves on the board, terminal board
  * one for the search: everything concerning the hash map, the state, the search, winner, reporting
  * one for the plotting (see above)
  * one for `main`, the options, the option parsing

Answer
------

Done. The solver now starts at N=3 by default, uses quiet mode by default with --verbose to
print improving leaders, tracks and prints iteration counts before the move list, supports
--start N, and adds --plot to read the CSV and print an SVG score chart.

The code is split into the requested modules:

 - app/Tree.hs for Tree and tree operations
 - app/Game.hs for Board, Move, legal moves, move execution, terminal detection
 - app/Search.hs for hashmap-based exploration, winner tracking, reporting, CSV output
 - app/Plot.hs for CSV parsing and SVG rendering
 - app/Main.hs for options and program entry

I also removed RemovedTree, FrontierEntry, FrontierPop, and SuccessorPosition in favor of
tuples, and updated the CSV format to:

n,score,ratio,iterations,moves

--help, normal solving, --start, --verbose, and --plot all work with the refactored build.


2026-05-25 III
==============

We are changing the rules of the game.
Instead of arbitrary concatenation, only concatenations with a Leaf on the right are allowed
(`moveConcat t = Node t Leaf`).
The board is now a single tree plus the number of such concatenations still available as moves.
The moves do not need index information any longer.
They can be printed as just `c` (concatenation with a Leaf), `r` (rotate) `t` (tail),
and the move sequence does not need separating spaces but can just e.g. be `ccrtt`.

Preserve the old game and simulation and run it when command-line option `--full` is supplied.
Move the modules for the old game to `Full`: `module Full.Game` and `Full.Search`,
to make modules `Game` and `Search` available for the new game.

Without that option, the new game should be used.
The parameter N is then the number of concatenation moves available in the beginning,
and we start with N=1.
Scoring does not change (still the number of rotation moves).

Answer
------

Done. The solver now supports both rule sets:

 - Default mode uses the new reduced game in Game and Search:
  - board = one Tree plus remaining concat credits
  - Concat is only Node t Leaf
  - moves are c, r, t
  - move trails render compactly, e.g. ccrtt
  - default start is N=1
 - --full mode preserves the old indexed board game in Full.Game and Full.Search:
  - old board/list semantics
  - indexed moves like 0&0 r0 t0 ...
  - default start remains N=3

Main now routes between the two modes with --full, while --plot still reads the CSV and
renders SVG. The Cabal file was updated to include Full.Game and Full.Search.

I also verified:

 - default mode writes rows like 1,0,"0.00",3,"ct" and prints winners starting at N=1
 - --full still reproduces the old search/output style starting at N=3
 - --plot works with the shared CSV format n,score,ratio,iterations,moves


2026-05-26
==========

We introduce two new approximate searches for the highscore, for the new game:

1. Option `--random=NNN`.  This will for each `N` play `NNN` random games from the starting position and keep the winner.
   A random game is simply a game where a random move is chosen from the possible moves each time.
   The `NNN` argument defaults to 100000.
   Module: `Random`.

2. Option `--mcts=NNN`.  This will for each `N` play a game using Monte Carlo Tree Search (mcts) with random rollout.
   Each time the next move will be chosen after NNN mcts simulations (phases selection, expansion, rollout, backpropagation).
   The random rollout (use random game play from the given position from module `Random`, see above) determines the score
   of a new game tree leaf by the score obtained in the final position of the random rollout.
   The final "winner" is simply the game played by the mcts.
   Module: `MCTS`.

Answer
------

Added the two reduced-game approximate searches and wired them into the CLI.

 - Random: --random or --random=NNN runs repeated random playouts from each start board and
keeps the best result. Bare --random defaults to 100000 samples.
 - MCTS: --mcts or --mcts=NNN plays one reduced-game using Monte Carlo Tree Search, with NNN
simulations before each real move and random rollout from Random. Bare --mcts defaults to
100000 simulations per move.

The new modules are:

 - app/Random.hs
 - app/MCTS.hs

Main now routes reduced-game solving through:

 - exact search (Search) by default
 - Random with --random
 - MCTS with --mcts

--full still runs the old game via Full.Game and Full.Search, and --full is rejected if
combined with --random or --mcts. The CSV and SVG plotting flow stays unchanged.


2026-05-26 II
=============

Make me an interactive webpage (new folder `play/`, entry `play/index.html`) that simulates/visualizes the tree game.
The layout has 3 zones, arranged vertically.

The top zone (10%) displays counts of number of C, T, and R moves, and the ratio R/C (unless C is zero) with 2 decimal digits.  Make sure these numbers are right-aligned and do not shift position when they are changed (so each number needs its own cell that is fixed horizontally).

The middle zone (80%) displays the tree, only showing the `Node` part (`Leaf` omitted).  The root should be on top, nodes should be solid balls, and the lines should have some thickness. The picture of the tree should be zoomed to fill the middle zone (up to some margins).

The lower zone (10%) has a text input field that contains the string of moves e.g. "ccrtcr".
The focus should be on the text input, so that when the page is loaded one can directly type into the text input.
If its content changes in any way (e.g. by pressing c, r, or t, or backspacing, or pasting a new string there), the tree should be updated to be as computed from the move sequence in the text input, and the stats (C, T, R, ratio) in the top zone should be updated.
More precisely: the game status (tree, stats) should be determined by the move string up to the cursor position in the text field.  Characters after the cursor should be ignored.  This allows to go back and forward in the move sequence and see the tree changing without having to delete characters from the move sequence.

The horizontal alignment of the three zones should be centered.

It the move sequence is illegal, the middle zone should display a big red X and the stats should also display red Xs.

A second task: Change the Haskell program (modules `Search`, `Random`, `MCTS`) so that when a terminal position is reached with the same score as the current winner, the move sequence is kept that is smaller in the lexicographic order (standard `Ord` for the list of moves (`MoveTrail`)).

Answer
------

Added play/index.html: a self-contained interactive playground with the requested 3-zone
layout, fixed-width right-aligned stats, cursor-aware move parsing, SVG tree rendering,
autofocus on the move input, and red X feedback for illegal prefixes.

On the Haskell side, the reduced-game tie-break is updated so equal scores prefer the
lexicographically smaller move trail:

 - Search and Random now compare equal-score winners by MoveTrail.
 - Game.Move now derives Ord to support trail ordering.
 - MCTS now breaks equal reduced-game move-choice ties lexicographically.

The project still builds cleanly.


2026-05-26 III
==============

For the web page, make the following changes:
- The zones should be 10%,80%,10% of the frame height and change when the user resizes the window.  They should not grow with their content, rather their content should be fit into the zones.
- The top zone currently displays e.g. "C 3 T 0 R 1 R/C 0.33" but I want "3 C 0 T 1 R 0.33 R/C".

For the Haskell program, add a module `DFS` and option `--dfs` that implements depth-first search (rather than the breadth-first search we have in `Search`).
(This is a simple recursive function without any state beyond the current winner. No caching/hashing of visited position is needed.)
(The basic search logic remains the same: do iterative deepening, printing the winner for each depth, until the user kills the program.)

Answer
------

Done.

 - Web page: play/index.html now keeps the three zones at 10% / 80% / 10% of the viewport
height on resize, with content fitted inside those zones. The top stats are reordered to 3 C
0 T 1 R
  0.33 R/C with fixed-width right-aligned number cells.
 - Haskell: added app/DFS.hs and wired --dfs into the reduced-game CLI. It runs
iterative-deepening depth-first search, prints the best winner after each depth, and still
prefers the lexicographically smaller move trail on equal score.

--help now includes --dfs, and the project builds cleanly.
