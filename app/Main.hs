{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Control.Monad (unless, when)
import Data.Hashable (Hashable)
import Data.HashMap.Strict qualified as HashMap
import Data.List (intercalate)
import Data.Maybe (mapMaybe)
import GHC.Generics (Generic)
import Numeric (showFFloat)
import Options.Applicative
import System.Directory (doesFileExist)
import System.IO (IOMode (AppendMode), withFile, hPutStrLn)

-- | Number of leaves used to build the initial board of one game.
type LeafCount = Int

-- | Index into the current board.
type BoardIndex = Int

-- | Number of rotation moves performed along a move trail.
type RotationScore = Int

-- | Path of moves from the start position to the current position.
type MoveTrail = [Move]

-- | Output CSV file path.
type OutputPath = FilePath

-- | Binary tree values that appear on the board.
data Tree
  = Leaf
  -- ^ A leaf node.
  | Node Tree Tree
  -- ^ An internal node with left and right subtrees.
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)

-- | Sorted multiset of trees that forms a search position.
newtype Board = Board
  { boardTrees :: [Tree]
    -- ^ Trees kept in ascending order so equal positions normalize to one key.
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable)

-- | Player action applicable to a board position.
data Move
  = Concat BoardIndex BoardIndex
  -- ^ Remove one tree, then remove another tree from the shortened board, and
  -- insert their concatenation.
  | Rotate BoardIndex
  -- ^ Rotate the tree at the given index if it matches the rotation shape.
  | Tail BoardIndex
  -- ^ Drop a leading 'Leaf' from the tree at the given index when possible.
  deriving stock (Eq, Show)

-- | Result of removing one tree from the board.
data RemovedTree = RemovedTree
  { removedTree :: Tree
    -- ^ Tree taken from the board.
  , remainingBoard :: Board
    -- ^ Board after the indexed tree has been removed.
  }

-- | Search metadata attached to a board in the frontier.
data PositionInfo = PositionInfo
  { positionMovesRev :: MoveTrail
    -- ^ Move trail stored in reverse order for cheap extension.
  , positionScore :: RotationScore
    -- ^ Number of rotation moves contained in 'positionMovesRev'.
  }

-- | Best completed result found so far for one start size.
data Winner = Winner
  { winnerScore :: RotationScore
    -- ^ Highest number of rotations seen on a completed game.
  , winnerMoves :: MoveTrail
    -- ^ Move trail that achieves 'winnerScore'.
  }

-- | Mutable search state threaded through the pure graph exploration.
data SearchState = SearchState
  { searchFrontier :: HashMap.HashMap Board PositionInfo
    -- ^ Unexplored positions keyed by their normalized board.
  , searchBestScores :: HashMap.HashMap Board RotationScore
    -- ^ Best score ever seen for each board, used for dominance pruning.
  , searchWinner :: Maybe Winner
    -- ^ Best terminal result found so far, if any.
  }

-- | One board pulled out of the frontier for expansion.
data FrontierEntry = FrontierEntry
  { frontierBoard :: Board
    -- ^ Board selected for expansion.
  , frontierPosition :: PositionInfo
    -- ^ Search metadata associated with 'frontierBoard'.
  }

-- | Result of taking one entry out of the frontier hashmap.
data FrontierPop = FrontierPop
  { poppedEntry :: FrontierEntry
    -- ^ Entry chosen for expansion.
  , remainingFrontierMap :: HashMap.HashMap Board PositionInfo
    -- ^ Frontier after removing 'poppedEntry'.
  }

-- | One newly reached search position.
data SuccessorPosition = SuccessorPosition
  { successorBoard :: Board
    -- ^ Board reached by applying one legal move.
  , successorInfo :: PositionInfo
    -- ^ Trail and score associated with 'successorBoard'.
  }

-- | Command line options that control output behaviour.
data CommandLineOptions = CommandLineOptions
  { optionsQuiet :: Bool
    -- ^ Suppress intermediate leader updates when 'True'.
  , optionsOutputPath :: OutputPath
    -- ^ CSV file that receives one appended line per finished game.
  }

-- | Parse command line options and keep solving games until interrupted.
main :: IO ()
main = do
  options <- execParser commandLineParserInfo
  mapM_ (runSingleGame options) [0 ..]

-- | Run one game, print its winner, and append the result to CSV.
--
-- Precondition: the leaf count is non-negative.
-- Postcondition: exactly one CSV row for the finished game has been appended.
runSingleGame :: CommandLineOptions -> LeafCount -> IO ()
runSingleGame options leafCount = do
  winner <- solveGame options leafCount
  putStrLn ("winner " <> formatWinnerSummary leafCount winner)
  appendWinnerCsv (optionsOutputPath options) leafCount winner

-- | Explore the full game graph for the given start size.
--
-- Precondition: the leaf count is non-negative.
-- Postcondition: returns the highest-scoring completed game reachable from the
-- start board.
solveGame :: CommandLineOptions -> LeafCount -> IO Winner
solveGame options leafCount = searchLoop initialState
  where
    initialBoard = start leafCount
    initialPosition = PositionInfo [] 0

    initialState =
      SearchState
        { searchFrontier = HashMap.singleton initialBoard initialPosition
        , searchBestScores = HashMap.singleton initialBoard 0
        , searchWinner = Nothing
        }

    searchLoop searchState =
      case popFrontier (searchFrontier searchState) of
        Nothing ->
          pure $
            case searchWinner searchState of
              Just winner -> winner
              Nothing -> Winner 0 []
        Just FrontierPop {..} -> do
          let FrontierEntry {..} = poppedEntry
              baseState = searchState {searchFrontier = remainingFrontierMap}

          -- First record completed games before generating further successors.
          stateAfterWinner <-
            updateWinnerIfBetter
              options
              leafCount
              frontierBoard
              frontierPosition
              baseState

          -- Then expand every legal successor and keep only score-improving
          -- entries for boards that survive dominance pruning.
          let successorPositions = successorsFrom frontierBoard frontierPosition
              nextState = foldl' insertSuccessor stateAfterWinner successorPositions

          searchLoop nextState

-- | Create the initial board consisting only of leaves.
--
-- Precondition: the leaf count is non-negative.
-- Postcondition: the returned board is sorted.
start :: LeafCount -> Board
start leafCount = Board (replicate leafCount Leaf)

-- | Concatenate two trees into one parent node.
--
-- Postcondition: the result contains the two input trees as left and right
-- children respectively.
concatTree :: Tree -> Tree -> Tree
concatTree = Node

-- | Perform one left rotation if the tree has the required shape.
--
-- Postcondition: returns 'Nothing' exactly when the input tree is not
-- rotatable.
rotateTree :: Tree -> Maybe Tree
rotateTree (Node (Node leftTree middleTree) rightTree) =
  Just (Node leftTree (Node middleTree rightTree))
rotateTree _ = Nothing

-- | Drop a leading leaf from a tree if present.
--
-- Postcondition: returns 'Nothing' exactly when the input tree does not start
-- with 'Leaf' on the left.
tailTree :: Tree -> Maybe Tree
tailTree (Node Leaf subtree) = Just subtree
tailTree _ = Nothing

-- | Apply one move to a board.
--
-- Postcondition: returns 'Nothing' exactly when the move precondition fails.
move :: Move -> Board -> Maybe Board
move = \case
  Concat firstIndex secondIndex -> moveConcat firstIndex secondIndex
  Rotate boardIndex -> moveRotate boardIndex
  Tail boardIndex -> moveTail boardIndex

-- | Remove two trees and insert their concatenation.
--
-- Precondition: both indices refer to the boards described in the original
-- rules: the second index is interpreted on the board after removing the first
-- tree.
-- Postcondition: the returned board is sorted.
moveConcat :: BoardIndex -> BoardIndex -> Board -> Maybe Board
moveConcat firstIndex secondIndex board = do
  firstRemoval <- takeOutTree firstIndex board
  secondRemoval <- takeOutTree secondIndex (remainingBoard firstRemoval)
  pure $
    insertTree
      (concatTree (removedTree firstRemoval) (removedTree secondRemoval))
      (remainingBoard secondRemoval)

-- | Rotate the tree at the given index and insert the result back into the
-- sorted board.
--
-- Postcondition: the returned board is sorted.
moveRotate :: BoardIndex -> Board -> Maybe Board
moveRotate boardIndex board = do
  removed <- takeOutTree boardIndex board
  rotatedTree <- rotateTree (removedTree removed)
  pure (insertTree rotatedTree (remainingBoard removed))

-- | Take the tail of the tree at the given index and insert the result back
-- into the sorted board.
--
-- Postcondition: the returned board is sorted.
moveTail :: BoardIndex -> Board -> Maybe Board
moveTail boardIndex board = do
  removed <- takeOutTree boardIndex board
  tailedTree <- tailTree (removedTree removed)
  pure (insertTree tailedTree (remainingBoard removed))

-- | Remove the tree at the given index.
--
-- Precondition: the index is zero-based.
-- Postcondition: returns 'Nothing' when the index is out of bounds or
-- negative.
takeOutTree :: BoardIndex -> Board -> Maybe RemovedTree
takeOutTree boardIndex (Board trees) = go boardIndex trees
  where
    go 0 (tree : remainingTrees) =
      Just (RemovedTree tree (Board remainingTrees))
    go index (tree : remainingTrees)
      | index > 0 = do
          RemovedTree removed remainingBoard <- go (index - 1) remainingTrees
          pure
            ( RemovedTree
                removed
                (Board (tree : boardTrees remainingBoard))
            )
    go _ _ = Nothing

-- | Insert one tree into the board while preserving sorted order.
--
-- Postcondition: the returned board is sorted.
insertTree :: Tree -> Board -> Board
insertTree treeToInsert (Board trees) = Board (go trees)
  where
    go [] = [treeToInsert]
    go existingTrees@(tree : restTrees)
      | treeToInsert <= tree = treeToInsert : existingTrees
      | otherwise = tree : go restTrees

-- | Enumerate every legal move from a board.
--
-- Postcondition: every move in the result satisfies the corresponding move
-- precondition.
legalMoves :: Board -> [Move]
legalMoves board@(Board trees) =
  concat
    [ legalConcatMoves board
    , [Rotate boardIndex | (boardIndex, tree) <- zip [0 ..] trees, canRotate tree]
    , [Tail boardIndex | (boardIndex, tree) <- zip [0 ..] trees, canTail tree]
    ]

-- | Enumerate all concat moves whose indices are valid for the current board.
--
-- Postcondition: returns the empty list when the board holds fewer than two
-- trees.
legalConcatMoves :: Board -> [Move]
legalConcatMoves (Board trees) =
  [ Concat firstIndex secondIndex
  | firstIndex <- [0 .. treeCount - 1]
  , secondIndex <- [0 .. treeCount - 2]
  ]
  where
    treeCount = length trees

-- | Check whether a tree is rotatable.
canRotate :: Tree -> Bool
canRotate = \case
  Node (Node _ _) _ -> True
  _ -> False

-- | Check whether a tree admits the tail operation.
canTail :: Tree -> Bool
canTail = \case
  Node Leaf _ -> True
  _ -> False

-- | Expand one frontier position into all successor positions.
--
-- Postcondition: every successor contains an updated move trail and score.
successorsFrom :: Board -> PositionInfo -> [SuccessorPosition]
successorsFrom board positionInfo =
  mapMaybe applyMove (legalMoves board)
  where
    applyMove chosenMove = do
      nextBoard <- move chosenMove board
      let nextScore =
            positionScore positionInfo
              + moveScore chosenMove
          nextInfo =
            PositionInfo
              { positionMovesRev = chosenMove : positionMovesRev positionInfo
              , positionScore = nextScore
              }
      pure
        SuccessorPosition
          { successorBoard = nextBoard
          , successorInfo = nextInfo
          }

-- | Score contribution of a single move.
moveScore :: Move -> RotationScore
moveScore = \case
  Rotate _ -> 1
  Concat _ _ -> 0
  Tail _ -> 0

-- | Remove one arbitrary entry from the frontier hashmap.
--
-- Postcondition: the returned frontier no longer contains the popped board.
popFrontier :: HashMap.HashMap Board PositionInfo -> Maybe FrontierPop
popFrontier frontierMap =
  case HashMap.toList frontierMap of
    [] -> Nothing
    ((board, positionInfo) : _) ->
      Just
        FrontierPop
          { poppedEntry =
              FrontierEntry
                { frontierBoard = board
                , frontierPosition = positionInfo
                }
          , remainingFrontierMap = HashMap.delete board frontierMap
          }

-- | Insert a successor into the frontier when it improves the best known score
-- for its board.
--
-- Postcondition: the frontier contains at most one entry for each board, and
-- that entry has the highest score seen so far for that board.
insertSuccessor :: SearchState -> SuccessorPosition -> SearchState
insertSuccessor searchState SuccessorPosition {..}
  | alreadyDominated = searchState
  | otherwise =
      searchState
        { searchFrontier =
            HashMap.insert successorBoard successorInfo (searchFrontier searchState)
        , searchBestScores =
            HashMap.insert successorBoard successorScore (searchBestScores searchState)
        }
  where
    successorScore = positionScore successorInfo
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
  CommandLineOptions ->
  LeafCount ->
  Board ->
  PositionInfo ->
  SearchState ->
  IO SearchState
updateWinnerIfBetter options leafCount board positionInfo searchState
  | not (isCompletedBoard board) = pure searchState
  | not isBetter = pure searchState
  | otherwise = do
      unless (optionsQuiet options) $
        putStrLn ("leader " <> formatWinnerSummary leafCount candidateWinner)
      pure searchState {searchWinner = Just candidateWinner}
  where
    candidateWinner =
      Winner
        { winnerScore = positionScore positionInfo
        , winnerMoves = reverse (positionMovesRev positionInfo)
        }
    isBetter =
      case searchWinner searchState of
        Nothing -> True
        Just currentWinner -> winnerScore candidateWinner > winnerScore currentWinner

-- | Check whether a board counts as a completed game for winner purposes.
--
-- Postcondition: returns 'True' for the standard terminal board '[Leaf]' and
-- for the degenerate empty start board used when @N = 0@.
isCompletedBoard :: Board -> Bool
isCompletedBoard (Board [Leaf]) = True
isCompletedBoard (Board []) = True
isCompletedBoard _ = False

-- | Render a move in the user-requested textual syntax.
renderMove :: Move -> String
renderMove = \case
  Concat firstIndex secondIndex -> show firstIndex <> "&" <> show secondIndex
  Rotate boardIndex -> "r" <> show boardIndex
  Tail boardIndex -> "t" <> show boardIndex

-- | Render a move trail as a space-separated list.
renderMoveTrail :: MoveTrail -> String
renderMoveTrail = intercalate " " . map renderMove

-- | Format one winner line for terminal output.
formatWinnerSummary :: LeafCount -> Winner -> String
formatWinnerSummary leafCount Winner {..} =
  "N="
    <> show leafCount
    <> " score="
    <> show winnerScore
    <> " ratio="
    <> formatRatio leafCount winnerScore
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
appendWinnerCsv :: OutputPath -> LeafCount -> Winner -> IO ()
appendWinnerCsv outputPath leafCount winner = do
  fileExists <- doesFileExist outputPath
  withFile outputPath AppendMode $ \handle -> do
    when (not fileExists) $
      hPutStrLn handle "n,score,ratio,moves"
    hPutStrLn handle (winnerCsvRow leafCount winner)

-- | Convert one winner to a CSV row.
winnerCsvRow :: LeafCount -> Winner -> String
winnerCsvRow leafCount Winner {..} =
  intercalate
    ","
    [ show leafCount
    , show winnerScore
    , csvField (formatRatio leafCount winnerScore)
    , csvField (renderMoveTrail winnerMoves)
    ]

-- | Quote one CSV field and escape inner double quotes.
csvField :: String -> String
csvField text = "\"" <> concatMap escapeCharacter text <> "\""
  where
    escapeCharacter '"' = "\"\""
    escapeCharacter character = [character]

-- | Parser for all supported command line options.
commandLineParser :: Parser CommandLineOptions
commandLineParser =
  CommandLineOptions
    <$> switch
      ( long "quiet"
          <> short 'q'
          <> help "Suppress intermediate leader updates."
      )
    <*> strOption
      ( long "output"
          <> short 'o'
          <> metavar "FILE"
          <> value "score.csv"
          <> showDefault
          <> help "Append final winners to FILE."
      )

-- | Parser metadata used by 'execParser'.
commandLineParserInfo :: ParserInfo CommandLineOptions
commandLineParserInfo =
  info
    (commandLineParser <**> helper)
    ( fullDesc
        <> progDesc
          "Compute puzzle highscores for N = 0, 1, 2, ... until interrupted."
    )
