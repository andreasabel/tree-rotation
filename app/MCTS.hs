module MCTS
  ( SimulationCount
  , defaultMctsSimulations
  , solveGame
  ) where

import Game
  ( Board
  , LeafCount
  , Move (..)
  , isTerminalBoard
  , legalMoves
  , move
  , startBoard
  )
import Random qualified
import Search qualified
import System.Random (randomRIO)

-- | Number of MCTS simulations performed per real move choice.
type SimulationCount = Int

-- | Default number of MCTS simulations used before choosing each move.
defaultMctsSimulations :: SimulationCount
defaultMctsSimulations = 100000

-- | One MCTS node for a single reduced-game board.
data MctsNode = MctsNode
  { nodeBoard :: !Board
    -- ^ Board represented by this node.
  , nodeVisits :: !Int
    -- ^ Number of simulations that passed through this node.
  , nodeTotalReward :: !Double
    -- ^ Sum of rollout rewards from this node to terminal positions.
  , nodeUntriedMoves :: ![Move]
    -- ^ Legal moves that have not yet been expanded.
  , nodeChildren :: ![(Move, MctsNode)]
    -- ^ Expanded children keyed by the move from this node.
  }

-- | Play one reduced-game using MCTS to choose each real move.
--
-- Precondition: the start count is non-negative.
-- Postcondition: the returned winner is the actual game played by MCTS, and its
-- iteration count equals the total number of simulations performed.
solveGame :: Search.SearchOptions -> SimulationCount -> LeafCount -> IO Search.Winner
solveGame _ requestedSimulations leafCount =
  go (startBoard leafCount) [] 0 0
  where
    simulationsPerMove = max 1 requestedSimulations

    go board movesRev rotationScore totalSimulations
      | isTerminalBoard board =
          pure
            Search.Winner
              { Search.winnerScore = rotationScore
              , Search.winnerIterations = totalSimulations
              , Search.winnerMoves = reverse movesRev
              }
      | otherwise = do
          searchedRoot <- runSimulations simulationsPerMove (initialNode board)
          chosenMove <- chooseRealMove board searchedRoot
          case move chosenMove board of
            Just nextBoard ->
              go
                nextBoard
                (chosenMove : movesRev)
                (rotationScore + Search.moveScore chosenMove)
                (totalSimulations + simulationsPerMove)
            Nothing ->
              ioError (userError "Internal error: MCTS selected an illegal move.")

-- | Create a fresh tree node for a board.
initialNode :: Board -> MctsNode
initialNode board =
  MctsNode
    { nodeBoard = board
    , nodeVisits = 0
    , nodeTotalReward = 0
    , nodeUntriedMoves = legalMoves board
    , nodeChildren = []
    }

-- | Run the requested number of simulations from the root node.
runSimulations :: SimulationCount -> MctsNode -> IO MctsNode
runSimulations simulationCount = go simulationCount
  where
    go remainingSimulations rootNode
      | remainingSimulations <= 0 = pure rootNode
      | otherwise = do
          (_, updatedRoot) <- simulateNode rootNode
          go (remainingSimulations - 1) updatedRoot

-- | Perform one complete MCTS simulation from the given node.
--
-- Postcondition: the returned reward is the additional rotation score from this
-- node to a terminal board, and the returned node includes the simulation
-- update.
simulateNode :: MctsNode -> IO (Search.RotationScore, MctsNode)
simulateNode node
  | isTerminalBoard (nodeBoard node) =
      pure (0, node {nodeVisits = nodeVisits node + 1})
  | not (null (nodeUntriedMoves node)) = do
      (chosenMove, remainingMoves) <- pickRandomElement (nodeUntriedMoves node)
      case move chosenMove (nodeBoard node) of
        Just childBoard -> do
          (_, rolloutScore) <- Random.randomRollout childBoard
          let childNode =
                (initialNode childBoard)
                  { nodeVisits = 1
                  , nodeTotalReward = fromIntegral rolloutScore
                  }
              totalReward = Search.moveScore chosenMove + rolloutScore
              updatedNode =
                node
                  { nodeVisits = nodeVisits node + 1
                  , nodeTotalReward = nodeTotalReward node + fromIntegral totalReward
                  , nodeUntriedMoves = remainingMoves
                  , nodeChildren = (chosenMove, childNode) : nodeChildren node
                  }
          pure (totalReward, updatedNode)
        Nothing ->
          ioError (userError "Internal error: MCTS tried to expand an illegal move.")
  | otherwise = do
      let parentVisits = max 1 (nodeVisits node)
          chosenIndex = selectChildIndex parentVisits (nodeChildren node)
          (chosenMove, chosenChild) = nodeChildren node !! chosenIndex
      (childReward, updatedChild) <- simulateNode chosenChild
      let totalReward = Search.moveScore chosenMove + childReward
          updatedNode =
            node
              { nodeVisits = nodeVisits node + 1
              , nodeTotalReward = nodeTotalReward node + fromIntegral totalReward
              , nodeChildren =
                  replaceAt chosenIndex (chosenMove, updatedChild) (nodeChildren node)
              }
      pure (totalReward, updatedNode)

-- | Choose the move that MCTS will actually play from the current board.
--
-- Postcondition: returns one legal move for the current board.
chooseRealMove :: Board -> MctsNode -> IO Move
chooseRealMove board rootNode =
  case nodeChildren rootNode of
    [] -> chooseRandomMove (legalMoves board)
    children -> pure (fst (bestVisitedChild children))

-- | Pick the child with the highest visit count, breaking ties by average
-- reward.
bestVisitedChild :: [(Move, MctsNode)] -> (Move, MctsNode)
bestVisitedChild (firstChild : remainingChildren) =
  foldl chooseBetterChild firstChild remainingChildren
  where
    chooseBetterChild currentBest challenger
      | childVisits challenger > childVisits currentBest = challenger
      | childVisits challenger == childVisits currentBest
          && childAverage challenger > childAverage currentBest =
          challenger
      | childVisits challenger == childVisits currentBest
          && childAverage challenger == childAverage currentBest
          && fst challenger < fst currentBest =
          challenger
      | otherwise = currentBest

    childVisits (_, childNode) = nodeVisits childNode
    childAverage (_, childNode)
      | nodeVisits childNode == 0 = 0
      | otherwise = nodeTotalReward childNode / fromIntegral (nodeVisits childNode)
bestVisitedChild [] = error "bestVisitedChild called with an empty list"

-- | Select one child index using the UCB1 rule.
selectChildIndex :: Int -> [(Move, MctsNode)] -> Int
selectChildIndex parentVisits children =
  case scoredChildren of
    firstScoredChild : remainingScoredChildren ->
      thirdOf (foldl chooseBetterChild firstScoredChild remainingScoredChildren)
    [] -> 0
  where
    scoredChildren =
      zipWith
        (\childIndex child -> (ucbScore parentVisits child, fst child, childIndex))
        [0 ..]
        children

    chooseBetterChild bestChild challenger
      | scoreOf challenger > scoreOf bestChild = challenger
      | scoreOf challenger == scoreOf bestChild
          && moveOf challenger < moveOf bestChild =
          challenger
      | otherwise = bestChild

    scoreOf (score, _, _) = score
    moveOf (_, chosenMove, _) = chosenMove
    thirdOf (_, _, childIndex) = childIndex

-- | Compute the UCB1 score for one child edge.
ucbScore :: Int -> (Move, MctsNode) -> Double
ucbScore parentVisits (edgeMove, childNode) =
  immediateReward + averageReward + explorationBonus
  where
    immediateReward = fromIntegral (Search.moveScore edgeMove)
    averageReward
      | nodeVisits childNode == 0 = 0
      | otherwise = nodeTotalReward childNode / fromIntegral (nodeVisits childNode)
    explorationBonus =
      sqrt
        ( 2
            * log (fromIntegral (max 1 parentVisits))
            / fromIntegral (max 1 (nodeVisits childNode))
        )

-- | Replace the element at the given index.
replaceAt :: Int -> a -> [a] -> [a]
replaceAt 0 replacement (_ : remainingItems) = replacement : remainingItems
replaceAt index replacement (item : remainingItems) =
  item : replaceAt (index - 1) replacement remainingItems
replaceAt _ _ [] = []

-- | Pick and remove one random element from a non-empty list.
--
-- Precondition: the input list is non-empty.
pickRandomElement :: [a] -> IO (a, [a])
pickRandomElement items = do
  chosenIndex <- randomRIO (0, length items - 1)
  case splitAt chosenIndex items of
    (leadingItems, chosenItem : trailingItems) ->
      pure (chosenItem, leadingItems <> trailingItems)
    _ ->
      ioError (userError "Internal error: pickRandomElement called with an empty list.")

-- | Choose one move uniformly at random from a non-empty list.
--
-- Precondition: the input list is non-empty.
chooseRandomMove :: [Move] -> IO Move
chooseRandomMove moves = do
  chosenIndex <- randomRIO (0, length moves - 1)
  pure (moves !! chosenIndex)
