{-# OPTIONS --safe #-}

-- Move execution with resource tracking

module ResourcedGame where

open import Library
open import Data.Nat.Properties using
  ( +-assoc; +-comm; +-identityʳ; *-distribʳ-+
  ; ≤-refl; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; module ≤-Reasoning)
import Data.Nat.Solver as Nat

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import Game using (Moves; C; R; T; ε; _∙_)
open import Counting using (count; count-compose; C:_T:_R:_)

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
  thm-counts C n t refl rewrite +-identityʳ kₐ = ≤-refl
  thm-counts T n (ε ∙ t) refl rewrite +-identityʳ kₜ = ≤-refl
  thm-counts R (suc n) ((t₁ ∙ t₂) ∙ t₃) refl = ≤-refl
  thm-counts ε n t refl = ≤-refl
  thm-counts (m ∙ m') n t {n'} {t'} eq with rmoves m (n ⨮ t) in rm | eq
  ... | nothing | ()
  ... | just (n₁ ⨮ u) | eq' rewrite count-compose m m' =
    let
      (C: c#  T: t#  R: r# ) = count m
      (C: c#' T: t#' R: r#') = count m'
      p₁ : r# + n₁ ≤ c# * kₐ + (t# * kₜ + n)
      p₁ = thm-counts m n t rm
      p₂ : r#' + n' ≤ c#' * kₐ + (t#' * kₜ + n₁)
      p₂ = thm-counts m' n₁ u eq'
      open ≤-Reasoning
    in
    begin
      (r# + r#') + n'                                    ≡⟨ +-assoc r# r#' n' ⟩
      r# + (r#' + n')                                    ≤⟨ +-monoʳ-≤ r# p₂ ⟩
      r# + (c#' * kₐ + (t#' * kₜ + n₁))                  ≡⟨ lem r# c#' kₐ t#' kₜ n₁ ⟩
      c#' * kₐ + (t#' * kₜ + (r# + n₁))                  ≤⟨ +-monoʳ-≤ (c#' * kₐ) (+-monoʳ-≤ (t#' * kₜ) p₁) ⟩
      c#' * kₐ + (t#' * kₜ + (c# * kₐ + (t# * kₜ + n)))  ≡⟨ rhs-compose c# t# c#' t#' n ⟩
      (c# + c#') * kₐ + ((t# + t#') * kₜ + n)
    ∎
    where
    -- These lemmata could be solved with the ring solver.

    lem : ∀ (r# c#' kₐ t#' kₜ n₁ : ℕ)
        → r# + (c#' * kₐ + (t#' * kₜ + n₁)) ≡ c#' * kₐ + (t#' * kₜ + (r# + n₁))
    lem r# c#' kₐ t#' kₜ n₁ = let open ≡-Reasoning in
      begin
      r# + (c#' * kₐ + (t#' * kₜ + n₁))  ≡⟨ sym (+-assoc r# (c#' * kₐ) (t#' * kₜ + n₁)) ⟩
      (r# + c#' * kₐ) + (t#' * kₜ + n₁)  ≡⟨ cong (_+ (t#' * kₜ + n₁)) (+-comm r# (c#' * kₐ)) ⟩
      (c#' * kₐ + r#) + (t#' * kₜ + n₁)  ≡⟨ +-assoc (c#' * kₐ) r# (t#' * kₜ + n₁) ⟩
      c#' * kₐ + (r# + (t#' * kₜ + n₁))  ≡⟨ cong (c#' * kₐ +_) (sym (+-assoc r# (t#' * kₜ) n₁)) ⟩
      c#' * kₐ + ((r# + t#' * kₜ) + n₁)  ≡⟨ cong (λ k → c#' * kₐ + (k + n₁)) (+-comm r# (t#' * kₜ)) ⟩
      c#' * kₐ + ((t#' * kₜ + r#) + n₁)  ≡⟨ cong (c#' * kₐ +_) (+-assoc (t#' * kₜ) r# n₁) ⟩
      c#' * kₐ + (t#' * kₜ + (r# + n₁))
      ∎

    rhs-compose
      : ∀ c₁ t₁ c₂ t₂ n
      → c₂ * kₐ + (t₂ * kₜ + (c₁ * kₐ + (t₁ * kₜ + n)))
        ≡ (c₁ + c₂) * kₐ + ((t₁ + t₂) * kₜ + n)
    rhs-compose c₁ t₁ c₂ t₂ n = let open ≡-Reasoning in
      begin
        c₂ * kₐ + (t₂ * kₜ + (c₁ * kₐ + (t₁ * kₜ + n)))
      ≡⟨ cong (c₂ * kₐ +_) (sym (+-assoc (t₂ * kₜ) (c₁ * kₐ) (t₁ * kₜ + n))) ⟩
        c₂ * kₐ + ((t₂ * kₜ + c₁ * kₐ) + (t₁ * kₜ + n))
      ≡⟨ cong (λ k → c₂ * kₐ + (k + (t₁ * kₜ + n))) (+-comm (t₂ * kₜ) (c₁ * kₐ)) ⟩
        c₂ * kₐ + ((c₁ * kₐ + t₂ * kₜ) + (t₁ * kₜ + n))
      ≡⟨ sym (+-assoc (c₂ * kₐ) (c₁ * kₐ + t₂ * kₜ) (t₁ * kₜ + n)) ⟩
        (c₂ * kₐ + (c₁ * kₐ + t₂ * kₜ)) + (t₁ * kₜ + n)
      ≡⟨ cong (_+ (t₁ * kₜ + n)) (sym (+-assoc (c₂ * kₐ) (c₁ * kₐ) (t₂ * kₜ))) ⟩
        ((c₂ * kₐ + c₁ * kₐ) + t₂ * kₜ) + (t₁ * kₜ + n)
      ≡⟨ +-assoc (c₂ * kₐ + c₁ * kₐ) (t₂ * kₜ) (t₁ * kₜ + n) ⟩
        (c₂ * kₐ + c₁ * kₐ) + (t₂ * kₜ + (t₁ * kₜ + n))
      ≡⟨ cong ((c₂ * kₐ + c₁ * kₐ) +_) (sym (+-assoc (t₂ * kₜ) (t₁ * kₜ) n)) ⟩
        (c₂ * kₐ + c₁ * kₐ) + ((t₂ * kₜ + t₁ * kₜ) + n)
      ≡⟨ cong (λ k → k + ((t₂ * kₜ + t₁ * kₜ) + n)) (+-comm (c₂ * kₐ) (c₁ * kₐ)) ⟩
        (c₁ * kₐ + c₂ * kₐ) + ((t₂ * kₜ + t₁ * kₜ) + n)
      ≡⟨ cong (λ k → (c₁ * kₐ + c₂ * kₐ) + (k + n)) (+-comm (t₂ * kₜ) (t₁ * kₜ)) ⟩
        (c₁ * kₐ + c₂ * kₐ) + ((t₁ * kₜ + t₂ * kₜ) + n)
      ≡⟨ cong (λ k → k + ((t₁ * kₜ + t₂ * kₜ) + n)) (sym (*-distribʳ-+ kₐ c₁ c₂)) ⟩
        (c₁ + c₂) * kₐ + ((t₁ * kₜ + t₂ * kₜ) + n)
      ≡⟨ cong (λ k → (c₁ + c₂) * kₐ + (k + n)) (sym (*-distribʳ-+ kₜ t₁ t₂)) ⟩
        (c₁ + c₂) * kₐ + (((t₁ + t₂) * kₜ) + n)
      ∎


  thm-counts'
    : ∀ m n t {n' t'} (let (C: c# T: t# R: r#) = count m)
    → rmoves m (n ⨮ t) ≡ just (n' ⨮ t')
    → n' + r# ≤ n + (kₐ * c# + kₜ * t#)
  thm-counts' m n t {n'} {t'} eq = let (C: c# T: t# R: r#) = count m in begin
      n' + r#                 ≡⟨ +-comm n' r# ⟩
      r# + n'                 ≤⟨ thm-counts m n t eq  ⟩
      c# * kₐ + (t# * kₜ + n)  ≡⟨ solve 5 (λ c t n kₐ kₜ →
                                   c :* kₐ :+ (t :* kₜ :+ n) := n :+ (kₐ :* c :+ kₜ :* t))
                                 refl c# t# n kₐ kₜ ⟩
      n + (kₐ * c# + kₜ * t#)  ∎
   where open ≤-Reasoning; open Nat.+-*-Solver
