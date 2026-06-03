-- {-# OPTIONS --safe #-}  -- Restore when done

-- Agda proofs on optimal constant-time amortization theorem for catenable queues.

module Main where

open import Library
open import Tree
open import UpperBound using (amor-append; amor-tail; amor-rotate)
open import Game using (move; moves)
open import Sequence using (seq; thm-seq)
open import ResourcedGame using (_⨮_; rempty; module RMoves)
open import Sufficient using (Legal; thm-rmoves)
open import Counting using (count; C:_T:_R:_; thm-counts-seq)
import Necessary

-- Amortization theorem: pay 3 for each append and tail, then the rotations are also paid for.

kₐ : ℕ
kₐ = 2

kₜ : ℕ
kₜ = 2

amortization : ∀ {t t'}
  → (                     kₐ + Φ t + Φ t' ≥ Φ (t ∙ t'))
  × (tail t   ≡ just t' → kₜ + Φ t        ≥ Φ t')
  × (rotate t ≡ just t' → Φ t             ≥ 1 + Φ t')

amortization {t = t} {t' = t'} =
  amor-append {l = t} {r = t'} , amor-tail , amor-rotate

-- Lower bound.

-- There is a certain legal move sequence cycling on the empty tree.

move-sequence : ∀ m n → move (seq m n) ε ≡ just ε
move-sequence = thm-seq

-- A resource-aware execution of the move sequence succeeds as well
-- with the budgets as in the amortization theorem.
-- (Intuitively, if we replace C and T by +2 and R by -1 we stay non-negative throughout execution.)

-- We start with the empty tree an no resources and end up with the empty tree and some leftover resources.
resourced : ∀ m n → ∃ λ leftover → Legal (seq m n Game.ε) rempty (leftover ⨮ ε)
resourced m n with thm-rmoves (seq m n Game.ε) ε ε (move-sequence m n) 0 z≤n
... | leftover , _ , legal = leftover , legal

-- I calculated the leftover budget to 5m + n + 10 over a total allocation of Rs of 4nm + 10m + 4n + 12.

-- The ratio of R over C moves in this sequence approaches 4.
-- (Note that the total numbers of C and T moves coincide as we are cycling back to an empty tree.)

counting : ∀ m n → let
     c# = m * (n + 2) + n + 3
     r# = m * (4 * n + 3) + 3 * n + 2
  in count (seq m n Game.ε) ≡ (C: c# T: c# R: r#)
counting = thm-counts-seq

-- If any possible move sequence is also executable with resource constraints,
-- then kₐ + kₜ ≥ 4.

necessary
  : ∀ kₐ kₜ
  → (∀ ms t
     → moves ms ε ≡ just t
     → ∃ λ leftover → RMoves.rmoves kₐ kₜ ms rempty ≡ just (leftover ⨮ t))
  → kₐ + kₜ ≥ 4
necessary = Necessary.thm
