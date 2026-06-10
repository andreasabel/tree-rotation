{-# OPTIONS --safe #-}

module Tree where

open import Library

data Tree : Set where
  ε   : Tree
  _∙_ : (t₁ t₂ : Tree) → Tree

variable
  t t' t₁ t₂ : Tree

rotate : Tree → Maybe Tree
rotate ((t₁ ∙ t₂) ∙ t₃) = just (t₁ ∙ (t₂ ∙ t₃))
rotate _ = nothing

tail : Tree → Maybe Tree
tail (ε ∙ t) = just t
tail _       = nothing

-- General tools

-- Degenerate tree, left leaning.

left-spine : ℕ → Tree
left-spine zero    = ε
left-spine (suc n) = left-spine n ∙ ε

-- Degenerate tree, right leaning.

right-spine : ℕ → Tree
right-spine zero    = ε
right-spine (suc n) = ε ∙ right-spine n

-- Potential

module Potential where
  open ℕ

  Φᵣ : Tree → ℕ
  Φᵣ ε = 0
  Φᵣ (l ∙ r) = suc (Φᵣ l) ⊔ pred (Φᵣ r)

  Φₗ : Tree → ℕ
  Φₗ ε = 0
  Φₗ (l ∙ r) = suc (Φₗ l) ⊔ Φᵣ r

  Φ : Tree → ℕ
  Φ ε = 0
  Φ (l ∙ r) = suc (Φₗ l) ⊔ pred (Φᵣ r)

-- Pair something with a resource (in ℕ).

record Resourced (A : Set) : Set where
  constructor _⨮_  -- C-x 8 RET 2a2e
  field
    resources : ℕ
    payload   : A
infixl 4  _⨮_
