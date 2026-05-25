{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module Game
  ( LeafCount
  , MoveTrail
  , Board (..)
  , Move (..)
  , startBoard
  , move
  , legalMoves
  , isTerminalBoard
  , renderMove
  , renderMoveTrail
  ) where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Tree
  ( Tree
  , Tree (..)
  , canRotateTree
  , canTailTree
  , rotateTree
  , tailTree
  )

-- | Number of initial concat-with-leaf moves available in one reduced game.
type LeafCount = Int

-- | Path of moves from the start position to the current position.
type MoveTrail = [Move]

-- | Search position for the reduced game: one tree and the number of remaining
-- concat-with-leaf moves.
data Board = Board
  { boardTree :: Tree
    -- ^ Current tree manipulated by rotate and tail moves.
  , boardRemainingConcats :: Int
    -- ^ Number of concat-with-leaf moves still available.
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable)

-- | Player action applicable to the reduced game.
data Move
  = Concat
  -- ^ Replace the current tree @t@ with @Node t Leaf@ and consume one concat.
  | Rotate
  -- ^ Rotate the current tree if it matches the rotation shape.
  | Tail
  -- ^ Drop a leading 'Leaf' from the current tree when possible.
  deriving stock (Eq, Show)

-- | Create the initial reduced-game board.
--
-- Precondition: the count is non-negative.
-- Postcondition: the returned board has a single 'Leaf' and the requested
-- number of available concat moves.
startBoard :: LeafCount -> Board
startBoard leafCount =
  Board
    { boardTree = Leaf
    , boardRemainingConcats = leafCount
    }

-- | Apply one move to a board.
--
-- Postcondition: returns 'Nothing' exactly when the move precondition fails.
move :: Move -> Board -> Maybe Board
move = \case
  Concat -> moveConcat
  Rotate -> moveRotate
  Tail -> moveTail

-- | Replace the current tree @t@ with @Node t Leaf@ and decrease the remaining
-- concat count.
--
-- Postcondition: returns 'Nothing' exactly when no concat moves remain.
moveConcat :: Board -> Maybe Board
moveConcat board@(Board tree remainingConcats)
  | remainingConcats <= 0 = Nothing
  | otherwise =
      Just
        board
          { boardTree = Node tree Leaf
          , boardRemainingConcats = remainingConcats - 1
          }

-- | Rotate the current tree.
--
-- Postcondition: returns 'Nothing' exactly when the current tree is not
-- rotatable.
moveRotate :: Board -> Maybe Board
moveRotate board@(Board tree _) = do
  rotatedTree <- rotateTree tree
  pure board {boardTree = rotatedTree}

-- | Take the tail of the current tree.
--
-- Postcondition: returns 'Nothing' exactly when the current tree does not
-- admit the tail operation.
moveTail :: Board -> Maybe Board
moveTail board@(Board tree _) = do
  tailedTree <- tailTree tree
  pure board {boardTree = tailedTree}

-- | Enumerate every legal move from the reduced game position.
--
-- Postcondition: every move in the result satisfies the corresponding move
-- precondition.
legalMoves :: Board -> [Move]
legalMoves (Board tree remainingConcats) =
  concatMoves ++ rotateMoves ++ tailMoves
  where
    concatMoves = [Concat | remainingConcats > 0]
    rotateMoves = [Rotate | canRotateTree tree]
    tailMoves = [Tail | canTailTree tree]

-- | Check whether a board counts as a completed game.
--
-- Postcondition: returns 'True' exactly when no move is legal.
isTerminalBoard :: Board -> Bool
isTerminalBoard = null . legalMoves

-- | Render a move in the requested compact syntax.
renderMove :: Move -> String
renderMove = \case
  Concat -> "c"
  Rotate -> "r"
  Tail -> "t"

-- | Render a move trail as a compact string.
renderMoveTrail :: MoveTrail -> String
renderMoveTrail = concatMap renderMove
