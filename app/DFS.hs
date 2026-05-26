module DFS
  ( solveGame
  ) where

import Game
  ( Board
  , LeafCount
  , Move (..)
  , MoveTrail
  , isTerminalBoard
  , legalMoves
  , move
  , startBoard
  )
import Search qualified

-- | Explore the reduced game with plain depth-first search.
--
-- Precondition: the start count is non-negative.
-- Postcondition: returns the best terminal winner reachable from the start
-- board.
solveGame :: Search.SearchOptions -> LeafCount -> IO Search.Winner
solveGame _ leafCount =
  case search initialBoard [] 0 Nothing of
    (Just winner, totalIterations) ->
      pure winner {Search.winnerIterations = totalIterations}
    (Nothing, totalIterations) ->
      pure
        Search.Winner
          { Search.winnerScore = 0
          , Search.winnerIterations = totalIterations
          , Search.winnerMoves = []
          }
  where
    initialBoard = startBoard leafCount

-- | Perform one DFS and return the best winner seen so far.
--
-- Postcondition: the returned iteration count is the number of recursive calls
-- made during this traversal.
search ::
  Board ->
  MoveTrail ->
  Search.RotationScore ->
  Maybe Search.Winner ->
  (Maybe Search.Winner, Search.IterationCount)
search board movesRev rotationScore currentWinner
  | isTerminalBoard board =
      (updateWinner rotationScore movesRev currentWinner, 1)
  | otherwise =
      foldl
        step
        (currentWinner, 1)
        (legalMoves board)
  where
    step (bestWinner, totalIterations) chosenMove =
      case move chosenMove board of
        Just nextBoard ->
          let (nextWinner, nextIterations) =
                search
                  nextBoard
                  (chosenMove : movesRev)
                  (rotationScore + moveScore chosenMove)
                  bestWinner
           in (nextWinner, totalIterations + nextIterations)
        Nothing -> (bestWinner, totalIterations)

-- | Update the best winner with a newly reached terminal trail.
--
-- Postcondition: higher score wins, and equal scores are broken by the
-- lexicographically smaller move trail.
updateWinner ::
  Search.RotationScore ->
  MoveTrail ->
  Maybe Search.Winner ->
  Maybe Search.Winner
updateWinner rotationScore movesRev currentWinner =
  case currentWinner of
    Nothing -> Just candidateWinner
    Just winner
      | winnerBeats candidateWinner winner -> Just candidateWinner
      | otherwise -> currentWinner
  where
    candidateWinner =
      Search.Winner
        { Search.winnerScore = rotationScore
        , Search.winnerIterations = 0
        , Search.winnerMoves = reverse movesRev
        }

-- | Compare two winners using score first and lexicographic move order second.
winnerBeats :: Search.Winner -> Search.Winner -> Bool
winnerBeats candidateWinner currentWinner =
  Search.winnerScore candidateWinner > Search.winnerScore currentWinner
    || ( Search.winnerScore candidateWinner == Search.winnerScore currentWinner
           && Search.winnerMoves candidateWinner < Search.winnerMoves currentWinner
       )

-- | Score contribution of one move.
moveScore :: Move -> Search.RotationScore
moveScore Rotate = 1
moveScore Concat = 0
moveScore Tail = 0
