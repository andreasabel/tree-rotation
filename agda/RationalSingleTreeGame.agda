{-# OPTIONS --safe #-}

-- Move execution with resource tracking in the rational numbers.

module RationalSingleTreeGame where

open import Library hiding (_+_; _*_; _≤_)
open import Data.Nat using () renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import Agda.Builtin.Int renaming (pos to ℤfromℕ)
open import Data.Nat.Coprimality using (1-coprimeTo)
open import Data.Rational
open import Data.Rational.Literals using (fromℤ)
open import Data.Rational.Properties using
  ( +-identityˡ; +-assoc
  ; ≤-reflexive; +-monoʳ-≤; module ≤-Reasoning)
import Data.Rational.Tactic.RingSolver as ℚ

open import Tree using (Tree; ε; _∙_; tail; rotate)
open import SingleTreeGame using (Moves; C; R; T; ε; _∙_)
open import Counting using (count; count-compose; C:_T:_R:_)

-- Embed ℕ into ℚ.

fromℕ : ℕ → ℚ
fromℕ n = fromℤ (ℤfromℕ n)
-- mkℚ (ℤfromℕ n) 0 (Data.Nat.Coprimality.sym (1-coprimeTo n))
-- fromℕ n = ℤfromℕ n / 1 -- mkℚ (ℤfromℕ n) 0 (Data.Nat.Coprimality.sym (1-coprimeTo n))

-- fromℕ-hom : ∀ m n → fromℕ (m ℕ+ n) ≡ fromℕ m + fromℕ n
-- fromℕ-hom zero n = sym (+-identityˡ (fromℕ n))
-- fromℕ-hom (suc m) n = {!!}

-- TODO: replace this inductive definition by the more idiomatic fromℕ
[_]ℚ : ℕ → ℚ
[ zero  ]ℚ = 0ℚ
[ suc n ]ℚ = 1ℚ + [ n ]ℚ

-- TODO: fix this proof
[+]ℚ : ∀ a b → [ a ℕ+ b ]ℚ ≡ [ a ]ℚ + [ b ]ℚ
[+]ℚ zero    b = sym (+-identityˡ [ b ]ℚ)
[+]ℚ (suc a) b
  = trans (cong (1ℚ +_) ([+]ℚ a b))
          (sym (+-assoc 1ℚ [ a ]ℚ [ b ]ℚ))

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
rempty = 0ℚ ⨮ ε

-- Execute moves on resourced trees if possible,
-- for the given budget kₐ for concat and kₜ for tail.
-- A rotation costs 1 and is thus only executable if the bank account is ≥ 1.

module RMoves (kₐ kₜ : ℚ) where

  rmoves : Moves → RT → Maybe RT
  rmoves C (q ⨮ t) = just (kₐ + q ⨮ t ∙ ε)
  rmoves T (q ⨮ t) = Maybe.map (kₜ + q ⨮_) (tail t)
  rmoves R (q ⨮ t) with q ≥? 1ℚ
  ... | yes _ = Maybe.map ((q - 1ℚ) ⨮_) (rotate t)
  ... | no  _ = nothing
  rmoves ε = just
  rmoves (m ∙ m') = rmoves m >=> rmoves m'

  -- For resourced runs,
  -- the number of R moves is bounded by the number of C + T moves based on budgets.

  thm-counts
    : ∀ m q t {q' t'} (let (C: c# T: t# R: r#) = count m)
    → rmoves m (q ⨮ t) ≡ just (q' ⨮ t')
    → [ r# ]ℚ + q' ≤ [ c# ]ℚ * kₐ + ([ t# ]ℚ * kₜ + q)
  thm-counts C q t refl = ≤-reflexive (step kₐ kₜ q)
    where
    step : ∀ kₐ kₜ q → [ 0 ]ℚ + (kₐ + q) ≡ [ 1 ]ℚ * kₐ + ([ 0 ]ℚ * kₜ + q)
    step = ℚ.solve-∀

  thm-counts T q (ε ∙ t) refl = ≤-reflexive (step kₐ kₜ q)
    where
    step : ∀ kₐ kₜ q → [ 0 ]ℚ + (kₜ + q) ≡ [ 0 ]ℚ * kₐ + ([ 1 ]ℚ * kₜ + q)
    step = ℚ.solve-∀

  thm-counts R q ε eq with q ≥? 1ℚ | eq
  ... | yes _ | ()
  ... | no  _ | ()
  thm-counts R q (ε ∙ _) eq with q ≥? 1ℚ | eq
  ... | yes _ | ()
  ... | no  _ | ()
  thm-counts R q ((t₁ ∙ t₂) ∙ t₃) eq with q ≥? 1ℚ | eq
  ... | yes _ | refl = ≤-reflexive (step kₐ kₜ q)
    where
    step : ∀ kₐ kₜ q → [ 1 ]ℚ + (q - 1ℚ) ≡ [ 0 ]ℚ * kₐ + ([ 0 ]ℚ * kₜ + q)
    step = ℚ.solve-∀
  ... | no  _ | ()

  thm-counts ε q t refl = ≤-reflexive (step kₐ kₜ q)
    where
    step : ∀ kₐ kₜ q → [ 0 ]ℚ + q ≡ [ 0 ]ℚ * kₐ + ([ 0 ]ℚ * kₜ + q)
    step = ℚ.solve-∀

  thm-counts (m ∙ m') q t {q'} {t'} eq with rmoves m (q ⨮ t) in rm | eq
  ... | nothing | ()
  ... | just (q₁ ⨮ u) | eq' rewrite count-compose m m' =
    let
      (C: c#  T: t#  R: r# ) = count m
      (C: c#' T: t#' R: r#') = count m'
      p₁ : [ r# ]ℚ + q₁ ≤ [ c# ]ℚ * kₐ + ([ t# ]ℚ * kₜ + q)
      p₁ = thm-counts m q t rm
      p₂ : [ r#' ]ℚ + q' ≤ [ c#' ]ℚ * kₐ + ([ t#' ]ℚ * kₜ + q₁)
      p₂ = thm-counts m' q₁ u eq'
      open ≤-Reasoning
    in
    begin
      [ r# ℕ+ r#' ]ℚ + q'
    ≡⟨ cong (_+ q') ([+]ℚ r# r#') ⟩
      ([ r# ]ℚ + [ r#' ]ℚ) + q'
    ≡⟨ +-assoc [ r# ]ℚ [ r#' ]ℚ q' ⟩
      [ r# ]ℚ + ([ r#' ]ℚ + q')
    ≤⟨ +-monoʳ-≤ [ r# ]ℚ p₂ ⟩
      [ r# ]ℚ + ([ c#' ]ℚ * kₐ + ([ t#' ]ℚ * kₜ + q₁))
    ≡⟨ step₁ [ r# ]ℚ ([ c#' ]ℚ * kₐ) ([ t#' ]ℚ * kₜ) q₁ ⟩
      [ c#' ]ℚ * kₐ + ([ t#' ]ℚ * kₜ + ([ r# ]ℚ + q₁))
    ≤⟨ +-monoʳ-≤ ([ c#' ]ℚ * kₐ) (+-monoʳ-≤ ([ t#' ]ℚ * kₜ) p₁) ⟩
      [ c#' ]ℚ * kₐ + ([ t#' ]ℚ * kₜ + ([ c# ]ℚ * kₐ + ([ t# ]ℚ * kₜ + q)))
    ≡⟨ step₂ kₐ kₜ [ c# ]ℚ [ t# ]ℚ [ c#' ]ℚ [ t#' ]ℚ q ⟩
      ([ c# ]ℚ + [ c#' ]ℚ) * kₐ + (([ t# ]ℚ + [ t#' ]ℚ) * kₜ + q)
    ≡⟨ cong₂ (λ a b → a * kₐ + (b * kₜ + q))
             (sym ([+]ℚ c# c#')) (sym ([+]ℚ t# t#')) ⟩
      [ c# ℕ+ c#' ]ℚ * kₐ + ([ t# ℕ+ t#' ]ℚ * kₜ + q)
    ∎
    where
    step₁ : (r c t q : ℚ) → r + (c + (t + q)) ≡ c + (t + (r + q))
    step₁ = ℚ.solve-∀

    step₂ : (kₐ kₜ c₁ t₁ c₂ t₂ q : ℚ)
          → c₂ * kₐ + (t₂ * kₜ + (c₁ * kₐ + (t₁ * kₜ + q))) ≡ (c₁ + c₂) * kₐ + ((t₁ + t₂) * kₜ + q)
    step₂ = ℚ.solve-∀
