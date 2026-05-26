{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module Full.Game
  ( LeafCount
  , BoardIndex
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
import Data.List (intercalate)
import GHC.Generics (Generic)
import Tree
  ( Tree (..)
  , canRotateTree
  , canTailTree
  , concatTree
  , rotateTree
  , tailTree
  )

-- | Number of leaves used to build the initial board of one game.
type LeafCount = Int

-- | Index into the current board.
type BoardIndex = Int

-- | Path of moves from the start position to the current position.
type MoveTrail = [Move]

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

-- | Create the initial board consisting only of leaves.
--
-- Precondition: the leaf count is non-negative.
-- Postcondition: the returned board is sorted.
startBoard :: LeafCount -> Board
startBoard leafCount = Board (replicate leafCount Leaf)

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
-- Precondition: both indices refer to the boards described in the multi-tree
-- rules: the second index is interpreted on the board after removing the first
-- tree.
-- Postcondition: the returned board is sorted.
moveConcat :: BoardIndex -> BoardIndex -> Board -> Maybe Board
moveConcat firstIndex secondIndex board = do
  (firstTree, boardAfterFirst) <- takeOutTree firstIndex board
  (secondTree, boardAfterSecond) <- takeOutTree secondIndex boardAfterFirst
  pure (insertTree (concatTree firstTree secondTree) boardAfterSecond)

-- | Rotate the tree at the given index and insert the result back into the
-- sorted board.
--
-- Postcondition: the returned board is sorted.
moveRotate :: BoardIndex -> Board -> Maybe Board
moveRotate boardIndex board = do
  (tree, boardWithoutTree) <- takeOutTree boardIndex board
  rotatedTree <- rotateTree tree
  pure (insertTree rotatedTree boardWithoutTree)

-- | Take the tail of the tree at the given index and insert the result back
-- into the sorted board.
--
-- Postcondition: the returned board is sorted.
moveTail :: BoardIndex -> Board -> Maybe Board
moveTail boardIndex board = do
  (tree, boardWithoutTree) <- takeOutTree boardIndex board
  tailedTree <- tailTree tree
  pure (insertTree tailedTree boardWithoutTree)

-- | Remove the tree at the given index.
--
-- Precondition: the index is zero-based.
-- Postcondition: returns 'Nothing' when the index is out of bounds or
-- negative.
takeOutTree :: BoardIndex -> Board -> Maybe (Tree, Board)
takeOutTree boardIndex (Board trees) = go boardIndex trees
  where
    go 0 (tree : remainingTrees) = Just (tree, Board remainingTrees)
    go index (tree : remainingTrees)
      | index > 0 = do
          (removedTree, Board remainingBoardTrees) <- go (index - 1) remainingTrees
          pure (removedTree, Board (tree : remainingBoardTrees))
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
    , [Rotate boardIndex | (boardIndex, tree) <- zip [0 ..] trees, canRotateTree tree]
    , [Tail boardIndex | (boardIndex, tree) <- zip [0 ..] trees, canTailTree tree]
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

-- | Check whether a board counts as a completed game.
--
-- Postcondition: returns 'True' for the standard terminal board '[Leaf]' and
-- for the degenerate empty board used when @N = 0@.
isTerminalBoard :: Board -> Bool
isTerminalBoard (Board [Leaf]) = True
isTerminalBoard (Board []) = True
isTerminalBoard _ = False

-- | Render a move in the textual syntax.
renderMove :: Move -> String
renderMove = \case
  Concat firstIndex secondIndex -> show firstIndex <> "&" <> show secondIndex
  Rotate boardIndex -> "r" <> show boardIndex
  Tail boardIndex -> "t" <> show boardIndex

-- | Render a move trail as a space-separated list.
renderMoveTrail :: MoveTrail -> String
renderMoveTrail = intercalate " " . map renderMove
