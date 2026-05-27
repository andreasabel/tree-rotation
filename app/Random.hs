module Random
  ( SimulationCount
  , defaultRandomGames
  , randomRollout
  , solveGame
  , solveFrom
  ) where

import Control.Monad (when)
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
import System.Random (randomRIO)

-- | Number of random playouts performed for one start size.
type SimulationCount = Int

-- | Default number of random games sampled per start size.
defaultRandomGames :: SimulationCount
defaultRandomGames = 100000

-- | Play one random game from the given position to a terminal board.
--
-- Postcondition: the returned move trail is legal from the input board, and the
-- returned score is the number of rotation moves in that trail.
randomRollout :: Board -> IO (MoveTrail, Search.RotationScore)
randomRollout board
  | isTerminalBoard board = pure ([], 0)
  | otherwise = do
      chosenMove <- chooseRandomMove (legalMoves board)
      case move chosenMove board of
        Just nextBoard -> do
          (restMoves, restScore) <- randomRollout nextBoard
          pure (chosenMove : restMoves, Search.moveScore chosenMove + restScore)
        Nothing ->
          ioError (userError "Internal error: legalMoves produced an illegal move.")

-- | Estimate the best game result by sampling many random playouts.
--
-- Precondition: the start count is non-negative.
-- Postcondition: the returned winner is the best score seen among all sampled
-- playouts, and its iteration count equals the number of sampled games.
solveGame :: Search.SearchOptions -> SimulationCount -> LeafCount -> IO Search.Winner
solveGame searchOptions requestedSamples leafCount =
  solveFrom searchOptions requestedSamples leafCount (startBoard leafCount) []

-- | Estimate the best game result by sampling many random playouts from an
-- already initialized single-tree board.
solveFrom :: Search.SearchOptions -> SimulationCount -> LeafCount -> Board -> MoveTrail -> IO Search.Winner
solveFrom searchOptions requestedSamples leafCount initialBoard initialMoves = do
  winner <- go 1 Nothing
  pure winner {Search.winnerIterations = sampleCount}
  where
    sampleCount = max 1 requestedSamples
    initialScore = sum (map Search.moveScore initialMoves)

    go sampleIndex bestWinner
      | sampleIndex > sampleCount =
          pure $
            case bestWinner of
              Just winner -> winner
              Nothing ->
                Search.Winner
                  { Search.winnerScore = initialScore
                  , Search.winnerIterations = sampleCount
                  , Search.winnerMoves = initialMoves
                  }
      | otherwise = do
          (moveTrail, rotationScore) <- randomRollout initialBoard
          let candidateWinner =
                Search.Winner
                  { Search.winnerScore = initialScore + rotationScore
                  , Search.winnerIterations = sampleIndex
                  , Search.winnerMoves = initialMoves <> moveTrail
                  }
              improvedWinner =
                case bestWinner of
                  Nothing -> Just candidateWinner
                  Just currentWinner
                   | Search.winnerBeats candidateWinner currentWinner ->
                        Just candidateWinner
                    | otherwise -> bestWinner

          when
            ( searchImproved bestWinner candidateWinner
                && Search.searchVerbose searchOptions
            )
            ( putStrLn
                ("leader " <> Search.formatWinnerSummary leafCount candidateWinner)
            )

          go (sampleIndex + 1) improvedWinner

    searchImproved Nothing _ = True
    searchImproved (Just currentWinner) candidateWinner =
      Search.winnerBeats candidateWinner currentWinner

-- | Choose one move uniformly at random from a non-empty list.
--
-- Precondition: the input list is non-empty.
chooseRandomMove :: [Move] -> IO Move
chooseRandomMove moves = do
  chosenIndex <- randomRIO (0, length moves - 1)
  pure (moves !! chosenIndex)
