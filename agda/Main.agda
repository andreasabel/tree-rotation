{-# OPTIONS --safe #-}

-- Agda proofs on optimal constant-time amortization theorem for catenable queues.

module Main where

open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Tree
open import UpperBound using (amor-append; amor-tail; amor-rotate)
open import Game using (move; seq; thm-seq)

-- Amortization theorem: pay 3 for each append and tail, then the rotations are also paid for.

kₐ : ℕ
kₐ = 3

kₜ : ℕ
kₜ = 3

amortization : ∀ {t t'}
  → (                     kₐ + Φ t + Φ t' ≥ 1 + Φ (t ∙ t'))
  × (tail t   ≡ just t' → kₜ + Φ t        ≥ 1 + Φ t')
  × (rotate t ≡ just t' → Φ t             ≥ 1 + Φ t')

amortization {t = t} {t' = t'} =
  amor-append {l = t} {r = t'} , amor-tail , amor-rotate

-- Lower bound.

-- There is a certain legal move sequence cycling on the empty tree.

move-sequence : ∀ m n → move (seq m n) ε ≡ just ε
move-sequence = thm-seq

-- TODO:

-- 1. A resource-aware execution of the move sequence succeeds as well
-- with the budgets as in the amortization theorem.
-- (More concretely, if we replace C and T by +2 and R by -1 we stay non-negative throughout execution.)
-- The proof should be a simple (?) induction over the moves using the potential function.

-- 2. The ratio of R over C moves in this sequence approaches 4.
-- (Note that the total numbers of C and T moves coincide as we are cycling back to an empty tree.)
-- I calculated the leftover budget to 5m + n + 10 over a total allocation of Rs of 4nm + 10m + 4n + 12.
