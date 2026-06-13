{-# OPTIONS --safe #-}

-- Agda proofs on optimal constant-time amortization theorem for catenable queues.

module Main where

open import Library
open import Tree
open import Sequence using (seq; thm-seq)
open import Counting using (count; C:_T:_R:_; thm-counts-seq)
import Approx
import Necessary
import MultiTreeGame
import RationalSingleTreeGame
import RationalApprox
import ResourcedSingleTreeGame
import SingleTreeGame
import Sufficient
import SufficientSingleTree
import UpperBound

-- Amortization theorem: save 2 for each append and tail, then the rotations are paid for.

module Amortization where
  open ℕ
  open Potential
  open UpperBound using (amor-append; amor-tail; amor-rotate)

  -- Budget for concatenation operation

  kₐ : ℕ
  kₐ = 2

  -- Budget for tail operation

  kₜ : ℕ
  kₜ = 2

  -- Lemma: The budgets are sufficient to compensate changes in potential.

  amortization : ∀ {t t'}
    → (                     kₐ + Φ t + Φ t' ≥ Φ (t ∙ t'))
    × (tail t   ≡ just t' → kₜ + Φ t        ≥ Φ t')
    × (rotate t ≡ just t' → Φ t             ≥ 1 + Φ t')

  amortization {t = t} {t' = t'} =
    amor-append {l = t} {r = t'} , amor-tail , amor-rotate

  -- Theorem: every possible move sequence succeeds under resourced execution
  -- if the full potential is available as resource.

  open MultiTreeGame using (Forest; ε^_; Φs; Φ-initial; Moves; run)
  open Sufficient using (Legal; thm-rmoves)

  sufficient
    : ∀ {m n} (mv : Moves m n) (ts : Forest m) (ts' : Forest n)
    → run mv ts ≡ just ts'
    → ∀ k → k ≥ Φs ts
    → ∃ λ k' → (k' ≥ Φs ts') × Legal mv (k ⨮ ts) (k' ⨮ ts')
  sufficient = thm-rmoves

  sufficient-initial
    : ∀ {m n} (mv : Moves m n) (let ts = ε^ m) (ts' : Forest n)
    → run mv ts ≡ just ts'
    → ∃ λ k' → Legal mv (0 ⨮ ts) (k' ⨮ ts')
  sufficient-initial {m = m} mv ts' h with thm-rmoves mv (ε^ m) ts' h 0 (Φ-initial m)
  ... | k' , _ , legal = k' , legal

-- A certain move sequence is our tool to prove lower bounds.

module Seq where
  open SingleTreeGame using (ε; move)
  open ℕ

  -- There is a certain legal move sequence cycling on the empty tree.

  move-sequence : ∀ m n → move (seq m n) ε ≡ just ε
  move-sequence = thm-seq

  -- The ratio of R over C moves in this sequence approaches 4.
  -- (Note that the total numbers of C and T moves coincide as we are cycling back to an empty tree.)

  counting : ∀ m n → let
       c# = m * (n + 2) + n + 3
       r# = m * (4 * n + 3) + 3 * n + 2
    in count (seq m n ε) ≡ (C: c# T: c# R: r#)
  counting = thm-counts-seq

-- Lower bound: Integer budgets
-- This part shows that kₐ + kₜ ≥ 4 if kₐ and kₜ are integral.

module Budget-ℕ where
  open SingleTreeGame using (ε; move; moves)
  open Seq using (move-sequence)
  open ResourcedSingleTreeGame using (rempty; module RMoves)
  open SufficientSingleTree using (Legal; thm-rmoves)
  open ℕ

  -- A resource-aware execution of the move sequence succeeds as well
  -- with the budgets as in the amortization theorem.
  -- (Intuitively, if we replace C and T by +2 and R by -1 we stay non-negative throughout execution.)

  -- We start with the empty tree an no resources and end up with the empty tree and some leftover resources.
  resourced : ∀ m n → ∃ λ leftover → Legal (seq m n ε) rempty (leftover ⨮ ε)
  resourced m n with thm-rmoves (seq m n ε) ε ε (move-sequence m n) 0 z≤n
  ... | leftover , _ , legal = leftover , legal

  -- I calculated the leftover budget to 5m + n + 10 over a total allocation of Rs of 4nm + 10m + 4n + 12.

  -- If any possible move sequence is also executable with resource constraints,

  ResourcedExecutionComplete : (kₐ kₜ : ℕ) → Set
  ResourcedExecutionComplete kₐ kₜ =
    ∀ ms t
    → moves ms ε ≡ just t
    → ∃ λ leftover → RMoves.rmoves kₐ kₜ ms rempty ≡ just (leftover ⨮ t)

  -- then kₐ + kₜ ≥ 4 (in ℕ).

  necessary
    : ∀ kₐ kₜ
    → ResourcedExecutionComplete kₐ kₜ
    → kₐ + kₜ ≥ 4
  necessary = Necessary.thm

  -- Lower limit: kₐ + kₜ approximates 4.
  -- This means for all N there is p/q ≤ 1/N such that  kₐ + kₜ ≥ 4 - p/q.
  -- We express the two inequations in terms of ℕ only.

  approximation
    : ∀ kₐ kₜ
    → ResourcedExecutionComplete kₐ kₜ
    → ∀ N → ∃ λ p → ∃ λ q
    → q ≥ N * p
    × q * (kₐ + kₜ) + p ≥ q * 4
  approximation kₐ kₜ hyp N = p , q , fraction , thm
    where
    open Approx N
    open Proofs kₐ kₜ hyp

-- Lower bound: Rational budgets

-- Same statement, sharpened over the rationals:
-- the budget kₐ + kₜ approximates 4 from below within 1/N for every N ≥ 1.

module Budget-ℚ where
  open SingleTreeGame using (ε; move; moves)
  open RationalSingleTreeGame using ([_]ℚ; _⨮_)
    renaming (rempty to remptyℚ; module RMoves to RMovesℚ)

  open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
    renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_
             ; _≤_ to _≤ℚ_; _≥_ to _≥ℚ_; _<_ to _<ℚ_)

  -- Resource-aware execution completeness over the rationals.

  ResourcedExecutionCompleteℚ : (kₐ kₜ : ℚ) → Set
  ResourcedExecutionCompleteℚ kₐ kₜ =
    ∀ ms t
    → moves ms ε ≡ just t
    → ∃ λ leftover → 0ℚ ≤ℚ leftover × RMovesℚ.rmoves kₐ kₜ ms remptyℚ ≡ just (leftover ⨮ t)

  -- For every N' there is 0 ≤ r < 1/(suc N') with kₐ + kₜ ≥ 4 - r.

  approximationℚ
    : ∀ kₐ kₜ
    → 0ℚ ≤ℚ kₐ → 0ℚ ≤ℚ kₜ
    → ResourcedExecutionCompleteℚ kₐ kₜ
    → ∀ N' → ∃ λ (r : ℚ)
            → 0ℚ ≤ℚ r
            × r *ℚ [ suc N' ]ℚ <ℚ 1ℚ
            × kₐ +ℚ kₜ ≥ℚ [ 4 ]ℚ -ℚ r
  approximationℚ kₐ kₜ kₐ-pos kₜ-pos hyp N' = theorem
    where open RationalApprox kₐ kₜ kₐ-pos kₜ-pos hyp (suc N')
