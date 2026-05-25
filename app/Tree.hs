{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Tree
  ( Tree (..)
  , concatTree
  , rotateTree
  , tailTree
  , canRotateTree
  , canTailTree
  ) where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)

-- | Binary tree values that appear on the board.
data Tree
  = Leaf
  -- ^ A leaf node.
  | Node Tree Tree
  -- ^ An internal node with left and right subtrees.
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)

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

-- | Check whether a tree is rotatable.
canRotateTree :: Tree -> Bool
canRotateTree (Node (Node _ _) _) = True
canRotateTree _ = False

-- | Check whether a tree admits the tail operation.
canTailTree :: Tree -> Bool
canTailTree (Node Leaf _) = True
canTailTree _ = False
