{-# OPTIONS --safe #-}

-- Potential function proves sufficiency of 2,2-budget

module Sufficient where

open import Library
open import Data.Nat.Properties using
  ( +-identityʳ; +-suc; +-assoc; +-comm
  ; ≤-refl; ≤-trans; ≤-pred; +-monoˡ-≤; +-monoʳ-≤; +-cancelʳ-≤; module ≤-Reasoning)

open import Tree using (Tree; ε; _∙_; tail; rotate; _⨮_)

open import UpperBound using (amor-append; amor-tail; amor-rotate)
open import MultiTreeGame using (Forest; Moves; C; R; T; ε; _∙_; run; RF; module RMoves; Φs)

open ≤-Reasoning

open RMoves 2 2

-- Legal moves
-- n - n' ≤ Φ t - Φ t'  so  n + Φ t' ≤ n' + Φ t
-- What we have left (n') should at least be what we started with minus the potential diff.

Legal : Moves m n → RF m → RF n → Set
Legal mv rf@(k ⨮ ts) rf'@(k' ⨮ ts')
  = rmoves mv rf ≡ just rf'
  × k' + Φs ts ≥ k + Φs ts'

-- Goal is to prove this theorem by induction on the moves ms:

Thm-RMoves
  = ∀ {m n} (mv : Moves m n) (ts : Forest m) (ts' : Forest n)
  → run mv ts ≡ just ts'
  → ∀ k → k ≥ Φs ts
  → ∃ λ k' → (k' ≥ Φs ts') × Legal mv (k ⨮ ts) (k' ⨮ ts')

-- Theorem: legal move sequences are resource-correct.
-- Prove by induction on mv:
thm-rmoves : Thm-RMoves
thm-rmoves = {!!}
