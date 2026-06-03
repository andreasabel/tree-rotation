{-# OPTIONS --allow-unsolved-metas #-}  -- Replace when done by {-# OPTIONS --safe #-}

-- Move execution with resource tracking

module ResourcedGame where

open import Library

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import Game using (Moves; C; R; T; ε; _∙_)
open import Counting using (count; C:_T:_R:_)

infixl 4  _⨮_
record Resourced (A : Set) : Set where
  constructor _⨮_  -- C-x 8 RET 2a2e
  field
    resources : ℕ
    payload   : A

RT = Resourced Tree

rempty : RT
rempty = 0 ⨮ ε

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

  -- The number of R moves is bounded by the number of C + T moves based on resources.

  thm-counts
    : ∀ m n t {n' t'} (let (C: c# T: t# R: r#) = count m)
    → rmoves m (n ⨮ t) ≡ just (n' ⨮ t')
    → r# + n' ≤ c# * kₐ + (t# * kₜ + n)
  thm-counts C n t refl = {!!}
  thm-counts T n (ε ∙ t) refl = {!!}
  thm-counts R (suc n) ((t₁ ∙ t₂) ∙ t₃) refl = {!≤-refl!}
  thm-counts ε n t refl = {!≤-refl!}
  thm-counts (m ∙ m') n t eq = {!!}
