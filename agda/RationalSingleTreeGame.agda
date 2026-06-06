{-# OPTIONS --safe #-}

-- Move execution with resource tracking in the rational numbers.

module RationalSingleTreeGame where

open import Library hiding (_+_; _*_; _≤_)
open import Data.Rational

open import Tree using (Tree; ε; _∙_; tail; rotate)
open import SingleTreeGame using (Moves; C; R; T; ε; _∙_)
open import Counting using (count; count-compose; C:_T:_R:_)

-- Pair something with a resource (in ℚ).

record Resourced (A : Set) : Set where
  constructor _⨮_  -- C-x 8 RET 2a2e
  field
    resources : ℚ
    payload   : A
infixl 4  _⨮_

-- A tree with a "bank account".

RT = Resourced Tree

-- Initial position: empty tree, empty account.

rempty : RT
rempty = rational-zero ⨮ ε   -- TODO: replace rational-zero by the correct term from the std-lib
  where
  rational-zero : ℚ
  rational-zero = ?


-- Execute moves on resourced trees if possible,
-- for the given budget kₐ for concat and kₜ for tail.
-- A rotation costs 1 and is thus only executable if the bank account is non-empty.

module RMoves (kₐ kₜ : ℚ) where

  rmoves : Moves → RT → Maybe RT
  rmoves C (q     ⨮ t) = just (kₐ + q ⨮ t ∙ ε)
  rmoves T (q     ⨮ t) = Maybe.map (kₜ + q ⨮_) (tail t)

  -- TODO: This matching on q has to be replaced by a test whether q ≥ 1
  -- and a subtraction.
  -- OLD:
  -- rmoves R (suc q ⨮ t) = Maybe.map (q ⨮_) (rotate t)
  -- rmoves R (zero  ⨮ t) = nothing
  -- NEW:
  rmoves R (q ⨮ t) = ?

  rmoves ε = just
  rmoves (m ∙ m') = rmoves m >=> rmoves m'

  -- For resourced runs,
  -- the number of R moves is bounded by the number of C + T moves based on budgets.

  thm-counts
    : ∀ m q t {q' t'} (let (C: c# T: t# R: r#) = count m)
    → rmoves m (q ⨮ t) ≡ just (q' ⨮ t')
    → r# + q' ≤ c# * kₐ + (t# * kₜ + q)  -- TODO: fix this statement to insert coercions from ℕ to ℚ
  thm-counts = ?  -- TODO: do this proof (now with ℚ)

{- OLD proof for ℕ
  thm-counts C q t refl rewrite +-identityʳ kₐ = ≤-refl
  thm-counts T q (ε ∙ t) refl rewrite +-identityʳ kₜ = ≤-refl
  thm-counts R (suc q) ((t₁ ∙ t₂) ∙ t₃) refl = ≤-refl
  thm-counts ε q t refl = ≤-refl
  thm-counts (m ∙ m') q t {q'} {t'} eq with rmoves m (q ⨮ t) in rm | eq
  ... | nothing | ()
  ... | just (n₁ ⨮ u) | eq' rewrite count-compose m m' =
    let
      (C: c#  T: t#  R: r# ) = count m
      (C: c#' T: t#' R: r#') = count m'
      p₁ : r# + n₁ ≤ c# * kₐ + (t# * kₜ + q)
      p₁ = thm-counts m q t rm
      p₂ : r#' + q' ≤ c#' * kₐ + (t#' * kₜ + n₁)
      p₂ = thm-counts m' n₁ u eq'
      open ≤-Reasoning
    in
    begin
      (r# + r#') + q'                                    ≡⟨ +-assoc r# r#' q' ⟩
      r# + (r#' + q')                                    ≤⟨ +-monoʳ-≤ r# p₂ ⟩
      r# + (c#' * kₐ + (t#' * kₜ + n₁))                  ≡⟨ step₁ r# (c#' * kₐ) (t#' * kₜ) n₁ ⟩
      c#' * kₐ + (t#' * kₜ + (r# + n₁))                  ≤⟨ +-monoʳ-≤ (c#' * kₐ) (+-monoʳ-≤ (t#' * kₜ) p₁) ⟩
      c#' * kₐ + (t#' * kₜ + (c# * kₐ + (t# * kₜ + q)))  ≡⟨ step₂ kₐ kₜ c# t# c#' t#' q ⟩
      (c# + c#') * kₐ + ((t# + t#') * kₜ + q)
    ∎
    where
    step₁ : (r c t : ℕ) (q : ℚ)
          → r + (c + (t + q)) ≡ c + (t + (r + q))
    step₁ = Nat.solve-∀

    step₂ : (kₐ kₜ : ℚ) (c₁ t₁ c₂ t₂ : ℕ) (q : ℚ)
          → c₂ * kₐ + (t₂ * kₜ + (c₁ * kₐ + (t₁ * kₜ + q))) ≡ (c₁ + c₂) * kₐ + ((t₁ + t₂) * kₜ + q)
    step₂ = Nat.solve-∀
-}
