{-# OPTIONS --safe #-}

-- Move sequences operating on a list of trees.

module MultiTreeGame where

open import Library
open import Tree using (Tree; ε; _∙_)

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
data Move : (m n : ForestSize) → Set where
  -- create a unit tree
  U : Move m (1 + m)
  -- concatenate two trees (note this is impossible for m=0)
  C : (i : Fin (1 + m)) (j : Fin m) → Move (1 + m) m
  -- rotate a tree
  R : (i : Fin m) → Move m m
  -- take the tail of a tree
  T : (i : Fin m) → Move m m
  -- No moves
  ε : Move m m
  -- Concatenate two move sequences
  _∙_ : (mv₁ : Move l m) (mv₂ : Move m n) → Move l n

-- Executing a move sequence.

run : Move m n → Forest m → Maybe (Forest n)
run U ts = just (unit ts)
run (C i j) ts = just (concat i j ts)
run (R i) ts = rotate i ts
run (T i) ts = tail i ts
run ε ts = just ts
run (mv₁ ∙ mv₂) ts with run mv₁ ts
... | nothing = nothing
... | just ts₁ = run mv₂ ts₁
