{-# LANGUAGE BangPatterns #-}

module DFS
  ( solveGame
  , solveFrom
  ) where

import Game
  ( Board
  , LeafCount
  , MoveTrail
  , isTerminalBoard
  , legalMoves
  , move
  , startBoard
  )
import Search qualified

-- | Explore the single-tree game with plain depth-first search.
--
-- Precondition: the start count is non-negative.
-- Postcondition: returns the best terminal winner reachable from the start
-- board.
solveGame :: Search.SearchOptions -> LeafCount -> IO Search.Winner
solveGame searchOptions leafCount =
  solveFrom searchOptions leafCount (startBoard leafCount) []

-- | Explore the single-tree game with plain depth-first search from an already
-- initialized board.
solveFrom :: Search.SearchOptions -> LeafCount -> Board -> MoveTrail -> IO Search.Winner
solveFrom _ _ initialBoard initialMoves =
  let SearchResult winner totalIterations = search initialBoard []
   in pure
        winner
          { Search.winnerIterations = totalIterations
          , Search.winnerMoves = initialMoves <> Search.winnerMoves winner
          , Search.winnerScore = scoreMoveTrail initialMoves + Search.winnerScore winner
          }

-- | Result of one DFS traversal, including the best winner and the number of
-- recursive calls performed.
data SearchResult = SearchResult !Search.Winner !Search.IterationCount

-- | Combine two DFS results by keeping the better winner and summing the
-- iteration counts.
instance Semigroup SearchResult where
  SearchResult leftWinner leftIterations <> SearchResult rightWinner rightIterations =
    SearchResult bestWinner totalIterations
    where
      !bestWinner
        | Search.winnerBeats leftWinner rightWinner = leftWinner
        | otherwise = rightWinner
      !totalIterations = leftIterations + rightIterations

-- | Perform one DFS and return the best winner reachable from the current
-- board.
--
-- Postcondition: the returned iteration count is the number of recursive calls
-- made during this traversal.
search ::
  Board ->
  MoveTrail ->
  SearchResult
search board movesRev
  | isTerminalBoard board =
      SearchResult terminalWinner 1
  | otherwise =
      SearchResult bestWinner (childIterations + 1)
  where
    terminalWinner =
      Search.Winner
        { Search.winnerScore = scoreMoveTrail moveTrail
        , Search.winnerIterations = 0
        , Search.winnerMoves = moveTrail
        }
    !moveTrail = reverse movesRev
    SearchResult bestWinner childIterations =
      case childResults of
        firstResult : remainingResults ->
          foldl' (<>) firstResult remainingResults
        [] ->
          SearchResult terminalWinner 0
    childResults =
      [ search nextBoard (chosenMove : movesRev)
      | chosenMove <- legalMoves board
      , Just nextBoard <- [move chosenMove board]
      ]

-- | Compute the score of a complete move trail.
scoreMoveTrail :: MoveTrail -> Search.RotationScore
scoreMoveTrail = foldl' step 0
  where
    step !score chosenMove = score + Search.moveScore chosenMove
