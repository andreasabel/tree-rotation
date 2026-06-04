{-# OPTIONS --safe #-}

-- Prove that kₐ + kₜ ≥ 4 (in ℕ) is necessary to execute every move sequence.

open import Library
open import Tree using (ε)
open import Game using (moves)
open import Sequence using (seq; thm-seq)
open import ResourcedGame using (_⨮_; rempty; module RMoves)
open import Counting using (count; C:_T:_R:_)

module Necessary
  -- Budget for concat and tail.
  (kₐ kₜ : ℕ)
  -- We assume that this budget is sufficient to execute any legal move sequence.
  (hyp : ∀ mv t
   → moves mv ε ≡ just t
   → ∃ λ leftover → RMoves.rmoves kₐ kₜ mv rempty ≡ just (leftover ⨮ t))
  -- A move sequence that needs  kₐ + kₜ > 3.
  (let mv = seq 1 11 Game.ε)
  -- This sequence has the following move count:
  (let (C: c# T: t# R: r#) = count mv)
  -- Number of R moves r# = 82
  -- Number of C moves c# = 27
  -- Number of T moves t# = 27
  where

open import Data.Nat.Properties using
  ( +-identityʳ; *-comm
  ; *-monoˡ-≤ ; *-monoʳ-≤; ≤-refl; *-distribˡ-+; *-distribʳ-+; m≤n+m; n≮n; ≮⇒≥
  ; module ≤-Reasoning
  )
open ≤-Reasoning

open RMoves kₐ kₜ

-- The move sequence mv is executable, since very sequence ought to.
hmv : ∃ λ leftover → rmoves mv rempty ≡ just (leftover ⨮ ε)
hmv = hyp mv ε (thm-seq 1 11)

-- The resourced execution needs kₐ * 27 + kₜ * 27 ≥ 82.
-- Note that we do not formulate this as 27 * kₐ + 27 * kₜ ≥ 82
-- because this unfolds to a large expression Agda has problems dealing with.
counts-seq-1-11 : kₐ * c# + kₜ * t# ≥ r#
counts-seq-1-11 with hmv
... | leftover , run =
  begin
    r#
  ≤⟨ m≤n+m r# leftover ⟩
    leftover + r#
  ≤⟨ thm-counts' mv 0 ε run ⟩
     kₐ * c# + kₜ * t#
  ∎

-- It follows that kₐ + kₜ ≤ 3 is impossible.
thm-op : kₐ + kₜ ≤ 3 → 82 ≤ 81
thm-op h = begin
  82                ≤⟨ counts-seq-1-11 ⟩
  kₐ * 27 + kₜ * 27  ≡⟨ sym (*-distribʳ-+ 27 kₐ kₜ) ⟩
  (kₐ + kₜ) * 27     ≤⟨ *-monoˡ-≤ 27 h ⟩
  3 * 27            ∎

-- By decidability of ≤, we turn this into a positive statement.
thm : kₐ + kₜ ≥ 4
thm with 4 ≤? kₐ + kₜ
thm | yes p = p
thm | no ¬p = ⊥-elim (n≮n 81 (thm-op (≮⇒≥ ¬p)))
