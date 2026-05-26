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

-- | Explore the reduced game with iterative-deepening depth-first search.
--
-- Precondition: the start count is non-negative.
-- Postcondition: prints the best winner after each explored depth, and returns
-- the final winner once the full game tree has been covered.
solveGame :: Search.SearchOptions -> LeafCount -> IO Search.Winner
solveGame _ leafCount = go 0 Nothing 0
  where
    initialBoard = startBoard leafCount

    go depthLimit bestWinnerSoFar totalIterations = do
      let (bestWinnerAtDepth, depthIterations, sawCutoff) =
            depthLimitedSearch depthLimit initialBoard [] 0 bestWinnerSoFar
          cumulativeIterations = totalIterations + depthIterations
          reportedWinner =
            case bestWinnerAtDepth of
              Just winner ->
                winner {Search.winnerIterations = cumulativeIterations}
              Nothing ->
                Search.Winner
                  { Search.winnerScore = 0
                  , Search.winnerIterations = cumulativeIterations
                  , Search.winnerMoves = []
                  }

      putStrLn ("depth=" <> show depthLimit <> " winner " <> Search.formatWinnerSummary leafCount reportedWinner)

      if sawCutoff
        then go (depthLimit + 1) bestWinnerAtDepth cumulativeIterations
        else pure reportedWinner

-- | Perform one depth-limited DFS and return the best winner seen so far.
--
-- Postcondition: the returned iteration count is the number of recursive calls
-- made during this depth-limited traversal.
depthLimitedSearch ::
  Int ->
  Board ->
  MoveTrail ->
  Search.RotationScore ->
  Maybe Search.Winner ->
  (Maybe Search.Winner, Search.IterationCount, Bool)
depthLimitedSearch depthLimit board movesRev rotationScore currentWinner
  | isTerminalBoard board =
      (updateWinner rotationScore movesRev currentWinner, 1, False)
  | depthLimit <= 0 = (currentWinner, 1, True)
  | otherwise =
      foldl
        step
        (currentWinner, 1, False)
        (legalMoves board)
  where
    step (bestWinner, totalIterations, cutoffSeen) chosenMove =
      case move chosenMove board of
        Just nextBoard ->
          let (nextWinner, nextIterations, nextCutoff) =
                depthLimitedSearch
                  (depthLimit - 1)
                  nextBoard
                  (chosenMove : movesRev)
                  (rotationScore + moveScore chosenMove)
                  bestWinner
           in ( nextWinner
              , totalIterations + nextIterations
              , cutoffSeen || nextCutoff
              )
        Nothing -> (bestWinner, totalIterations, cutoffSeen)

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
