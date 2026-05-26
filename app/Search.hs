{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module Search
  ( IterationCount
  , RotationScore
  , SearchOptions (..)
  , Winner (..)
  , moveScore
  , winnerBeats
  , solveGame
  , formatWinnerSummary
  , appendWinnerCsv
  ) where

import Control.Monad (when)
import Data.HashMap.Strict qualified as HashMap
import Data.List (intercalate)
import Data.Maybe (mapMaybe)
import Game
  ( Board
  , LeafCount
  , Move (..)
  , MoveTrail
  , isTerminalBoard
  , legalMoves
  , move
  , renderMoveTrail
  , startBoard
  )
import Numeric (showFFloat)
import System.Directory (doesFileExist)
import System.IO (IOMode (AppendMode), hPutStrLn, withFile)

-- | Number of rotation moves performed along a move trail.
type RotationScore = Int

-- | Number of calls made to the search loop while solving one game.
type IterationCount = Int

-- | Reporting options that affect the search process.
data SearchOptions = SearchOptions
  { searchVerbose :: !Bool
    -- ^ Print each improving leader when 'True'.
  }

-- | Search metadata attached to a board in the frontier.
data PositionInfo = PositionInfo
  { positionMovesRev :: !MoveTrail
    -- ^ Move trail stored in reverse order for cheap extension.
  , positionScore :: !RotationScore
    -- ^ Number of rotation moves contained in 'positionMovesRev'.
  }

-- | Best completed result found so far for one start size.
data Winner = Winner
  { winnerScore :: !RotationScore
    -- ^ Highest number of rotations seen on a completed game.
  , winnerIterations :: !IterationCount
    -- ^ Number of search-loop calls used to establish the final answer.
  , winnerMoves :: !MoveTrail
    -- ^ Move trail that achieves 'winnerScore'.
  }

-- | Mutable search state threaded through the graph exploration.
data SearchState = SearchState
  { searchFrontier :: !(HashMap.HashMap Board PositionInfo)
    -- ^ Unexplored positions keyed by their normalized board.
  , searchBestScores :: !(HashMap.HashMap Board RotationScore)
    -- ^ Best score ever seen for each board, used for dominance pruning.
  , searchWinner :: !(Maybe Winner)
    -- ^ Best terminal result found so far, if any.
  , searchIterations :: !IterationCount
    -- ^ Number of completed calls to the main search loop.
  }

-- | Explore the full reduced-game graph for the given start size.
--
-- Precondition: the start count is non-negative.
-- Postcondition: returns the highest-scoring completed game reachable from the
-- start board.
solveGame :: SearchOptions -> LeafCount -> IO Winner
solveGame searchOptions leafCount = searchLoop initialState
  where
    initialBoard = startBoard leafCount
    initialPosition = PositionInfo [] 0

    initialState =
      SearchState
        { searchFrontier = HashMap.singleton initialBoard initialPosition
        , searchBestScores = HashMap.singleton initialBoard 0
        , searchWinner = Nothing
        , searchIterations = 0
        }

    searchLoop searchState0 =
      let searchState = searchState0 {searchIterations = searchIterations searchState0 + 1}
       in case popFrontier (searchFrontier searchState) of
            Nothing ->
              pure $
                case searchWinner searchState of
                  Just winner -> winner
                  Nothing ->
                    Winner
                      { winnerScore = 0
                      , winnerIterations = searchIterations searchState
                      , winnerMoves = []
                      }
            Just ((board, positionInfo), remainingFrontier) -> do
              let baseState = searchState {searchFrontier = remainingFrontier}

              -- First record completed games before generating further
              -- successors from the popped position.
              stateAfterWinner <-
                updateWinnerIfBetter
                  searchOptions
                  leafCount
                  board
                  positionInfo
                  baseState

              -- Then expand every legal successor and keep only score-improving
              -- entries for boards that survive dominance pruning.
              let successorPositions = successorsFrom board positionInfo
                  nextState = foldl insertSuccessor stateAfterWinner successorPositions

              searchLoop nextState

-- | Expand one frontier position into all successor positions.
--
-- Postcondition: every successor contains an updated move trail and score.
successorsFrom :: Board -> PositionInfo -> [(Board, PositionInfo)]
successorsFrom board positionInfo =
  mapMaybe applyMove (legalMoves board)
  where
    applyMove chosenMove = do
      nextBoard <- move chosenMove board
      let !nextScore = positionScore positionInfo + moveScore chosenMove
          nextInfo =
            PositionInfo
              { positionMovesRev = chosenMove : positionMovesRev positionInfo
              , positionScore = nextScore
              }
      pure (nextBoard, nextInfo)

-- | Score contribution of a single move.
moveScore :: Move -> RotationScore
moveScore Rotate = 1
moveScore Concat = 0
moveScore Tail = 0

-- | Remove one arbitrary entry from the frontier hashmap.
--
-- Postcondition: the returned frontier no longer contains the popped board.
popFrontier ::
  HashMap.HashMap Board PositionInfo ->
  Maybe ((Board, PositionInfo), HashMap.HashMap Board PositionInfo)
popFrontier frontierMap =
  case HashMap.toList frontierMap of
    [] -> Nothing
    ((board, positionInfo) : _) ->
      Just ((board, positionInfo), HashMap.delete board frontierMap)

-- | Insert a successor into the frontier when it improves the best known score
-- for its board.
--
-- Postcondition: the frontier contains at most one entry for each board, and
-- that entry has the highest score seen so far for that board.
insertSuccessor :: SearchState -> (Board, PositionInfo) -> SearchState
insertSuccessor searchState (successorBoard, successorInfo)
  | alreadyDominated = searchState
  | otherwise =
      searchState
        { searchFrontier =
            HashMap.insert successorBoard successorInfo (searchFrontier searchState)
        , searchBestScores =
            HashMap.insert successorBoard successorScore (searchBestScores searchState)
        }
  where
    !successorScore = positionScore successorInfo
    alreadyDominated =
      case HashMap.lookup successorBoard (searchBestScores searchState) of
        Just knownBestScore -> knownBestScore >= successorScore
        Nothing -> False

-- | Update the current winner when the popped board is a completed game with a
-- better score.
--
-- Postcondition: the winner is changed only when the candidate score is
-- strictly higher than the previous winner score.
updateWinnerIfBetter ::
  SearchOptions ->
  LeafCount ->
  Board ->
  PositionInfo ->
  SearchState ->
  IO SearchState
updateWinnerIfBetter searchOptions leafCount board positionInfo searchState
  | not (isTerminalBoard board) = pure searchState
  | not isBetter = pure searchState
  | otherwise = do
      when (searchVerbose searchOptions) $
        putStrLn ("leader " <> formatWinnerSummary leafCount candidateWinner)
      pure searchState {searchWinner = Just candidateWinner}
  where
    candidateWinner =
      Winner
        { winnerScore = positionScore positionInfo
        , winnerIterations = searchIterations searchState
        , winnerMoves = reverse (positionMovesRev positionInfo)
        }
    isBetter =
      case searchWinner searchState of
        Nothing -> True
        Just currentWinner -> winnerBeats candidateWinner currentWinner

-- | Decide whether the first winner is better than the second one.
--
-- Postcondition: higher score wins, and equal scores are broken by the
-- lexicographically smaller move trail.
winnerBeats :: Winner -> Winner -> Bool
winnerBeats candidateWinner currentWinner =
  winnerScore candidateWinner > winnerScore currentWinner
    || ( winnerScore candidateWinner == winnerScore currentWinner
           && winnerMoves candidateWinner < winnerMoves currentWinner
       )

-- | Format one winner line for terminal output.
formatWinnerSummary :: LeafCount -> Winner -> String
formatWinnerSummary leafCount Winner {..} =
  "N="
    <> show leafCount
    <> " score="
    <> show winnerScore
    <> " ratio="
    <> formatRatio leafCount winnerScore
    <> " iterations="
    <> show winnerIterations
    <> " moves="
    <> renderMoveTrail winnerMoves

-- | Format the requested score quotient with two decimal places.
--
-- Postcondition: returns @\"n/a\"@ when the leaf count is zero.
formatRatio :: LeafCount -> RotationScore -> String
formatRatio 0 _ = "n/a"
formatRatio leafCount rotationScore =
  showFFloat
    (Just 2)
    (fromIntegral rotationScore / fromIntegral leafCount :: Double)
    ""

-- | Append one finished game result to a CSV file, creating a header on first
-- use.
--
-- Postcondition: the file exists after the call completes successfully.
appendWinnerCsv :: FilePath -> LeafCount -> Winner -> IO ()
appendWinnerCsv outputPath leafCount winner = do
  fileExists <- doesFileExist outputPath
  withFile outputPath AppendMode $ \handle -> do
    when (not fileExists) $
      hPutStrLn handle "n,score,ratio,iterations,moves"
    hPutStrLn handle (winnerCsvRow leafCount winner)

-- | Convert one winner to a CSV row.
winnerCsvRow :: LeafCount -> Winner -> String
winnerCsvRow leafCount Winner {..} =
  intercalate
    ","
    [ show leafCount
    , show winnerScore
    , csvField (formatRatio leafCount winnerScore)
    , show winnerIterations
    , csvField (renderMoveTrail winnerMoves)
    ]

-- | Quote one CSV field and escape inner double quotes.
csvField :: String -> String
csvField text = "\"" <> concatMap escapeCharacter text <> "\""
  where
    escapeCharacter '"' = "\"\""
    escapeCharacter character = [character]
