{-# OPTIONS --safe #-}

module SingleTreeGame where

open import Library
open import Tree using (Tree; ε; _∙_; tail; rotate)

-- The tree game, with three possible moves C (concat), T (tail) and R (rotate)
-- to manipulate a single tree.

data Moves : Set where
  C T R : Moves
  ε     : Moves
  _∙_   : (m m' : Moves) → Moves

-- Running a move sequence.
-- Not every sequence is executable since T and R are not always available.

moves : Moves → Tree → Maybe Tree
moves C        = just ∘ (_∙ ε)
moves T        = tail
moves R        = rotate
moves ε        = just
moves (m ∙ m') = moves m >=> moves m'

-- The Cayley form of the Moves monoid, useful for definition repetitions.

M = Moves → Moves

move : M → Tree → Maybe Tree
move f = moves (f ε)

c : M
c m = C ∙ m

t : M
t m = T ∙ m

r : M
r m = R ∙ m
