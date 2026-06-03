{-# OPTIONS --safe #-}

-- Move execution with resource tracking

module ResourcedGame where

open import Library

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import Game using (Moves; C; R; T; ε; _∙_)

infixl 4  _⨮_
record Resourced (A : Set) : Set where
  constructor _⨮_  -- C-x 8 RET 2a2e
  field
    resources : ℕ
    payload   : A

RT = Resourced Tree

-- -- Updating the resources
-- rmap : {A : Set} → (ℕ → ℕ) → Resourced A → Resourced A
-- rmap f (n ⨮ a) = f n ⨮ a

-- rtmap : {A : Set} → (ℕ → ℕ) → Maybe RT → Maybe RT
-- rtmap f nothing = nothing
-- rtmap f (just (n ⨮ a)) = just (f n ⨮ a)

module RMoves (kₐ kₜ : ℕ) where

  rmoves : Moves → RT → Maybe RT
  rmoves C (n     ⨮ t) = just (kₐ + n ⨮ t ∙ ε)
  rmoves T (n     ⨮ t) = Maybe.map (kₜ + n ⨮_) (tail t)
  rmoves R (suc n ⨮ t) = Maybe.map (n ⨮_) (rotate t)
  rmoves R (zero  ⨮ t) = nothing
  rmoves ε = just
  rmoves (m ∙ m') = rmoves m >=> rmoves m'
