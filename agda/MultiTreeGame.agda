{-# OPTIONS --safe #-}

-- Move sequences operating on a list of trees.

module MultiTreeGame where

open import Library
open import Tree using (Tree; ε; _∙_; Resourced; _⨮_)

variable
  l m n : ℕ

-- The arena is a vector of trees

ForestSize = ℕ

Forest = Vec Tree

-- Select a tree from the forest

pick : Fin n → Forest n → ∃ λ m → n ≡ suc m × Tree × Forest m
pick zero (t ∷ ts) = _ , refl , t , ts
pick (suc i) (t' ∷ ts) with pick i ts
... | _ , refl , t , ts' = _ , refl , t , (t' ∷ ts')

-- Add an empty tree to the forest

unit : Forest m → Forest (1 + m)
unit ts = ε ∷ ts

-- Concatenate two trees from the forest

concat : (i : Fin (1 + m)) (j : Fin m) → Forest (1 + m) → Forest m
concat i j ts₀ with pick i ts₀
... | _ , refl , t₁ , ts₁ with pick j ts₁
... | _ , refl , t₂ , ts₂ = (t₁ ∙ t₂) ∷ ts₂

-- Rotate a tree in the forest; fails if tree is not rotateable

rotate : (i : Fin m) → Forest m → Maybe (Forest m)
rotate i ts with pick i ts
... | _ , refl , t₁ , ts₁ with Tree.rotate t₁
... | nothing = nothing
... | just t₂ = just (t₂ ∷ ts₁)

-- Take the tail of a tree in the forest; fails if left subtree is not empty

tail : (i : Fin m) → Forest m → Maybe (Forest m)
tail i ts with pick i ts
... | _ , refl , t₁ , ts₁ with Tree.tail t₁
... | nothing = nothing
... | just t₂ = just (t₂ ∷ ts₁)

-- Move sequences.

-- Individual moves pick 0..2 trees, operate on them, and place them back at the front.
data Moves : (m n : ForestSize) → Set where
  -- create a unit tree
  U : Moves m (1 + m)
  -- concatenate two trees (note this is impossible for m=0)
  C : (i : Fin (1 + m)) (j : Fin m) → Moves (1 + m) m
  -- rotate a tree
  R : (i : Fin m) → Moves m m
  -- take the tail of a tree
  T : (i : Fin m) → Moves m m
  -- No moves
  ε : Moves m m
  -- Concatenate two move sequences
  _∙_ : (mv₁ : Moves l m) (mv₂ : Moves m n) → Moves l n

-- Executing a move sequence.

run : Moves m n → Forest m → Maybe (Forest n)
run U           = just ∘ unit
run (C i j)     = just ∘ concat i j
run (R i)       = rotate i
run (T i)       = tail i
run ε           = just
run (mv₁ ∙ mv₂) = run mv₁ >=> run mv₂

-- Resourced execution

-- A forest with a "bank account".

RF : ForestSize → Set
RF n = Resourced (Forest n)

-- Initial position: empty forest, empty account.

rempty : RF 0
rempty = 0 ⨮ []

-- Execute moves on the resourced forest if possible,
-- for the given budget kₐ for concat and kₜ for tail.
-- A rotation costs 1 and is thus only executable if the bank account is non-empty.
-- Creation of empty trees is cost free.

module RMoves (kₐ kₜ : ℕ) where

  rmoves : Moves m n → RF m → Maybe (RF n)
  rmoves U       (k     ⨮ ts) = just (k ⨮ ε ∷ ts)
  rmoves (C i j) (k     ⨮ ts) = just (kₐ + k ⨮ concat i j ts)
  rmoves (T i)   (k     ⨮ ts) = Maybe.map (kₜ + k ⨮_) (tail i ts)
  rmoves (R i)   (suc k ⨮ ts) = Maybe.map (k ⨮_) (rotate i ts)
  rmoves (R _)   (zero  ⨮ ts) = nothing
  rmoves ε        = just
  rmoves (m ∙ m') = rmoves m >=> rmoves m'
