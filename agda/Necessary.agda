{-# OPTIONS --allow-unsolved-metas #-}  -- Replace by --safe when done

open import Library
open import Tree
open import Game using (move; moves)
open import Sequence using (seq; thm-seq)
open import ResourcedGame using (_⨮_; rempty; module RMoves)
open import Counting using (count; C:_T:_R:_; thm-counts-seq)

module Necessary
    (kₐ kₜ : ℕ)
    (hyp : ∀ mv t
     → moves mv ε ≡ just t
     → ∃ λ leftover → RMoves.rmoves kₐ kₜ mv rempty ≡ just (leftover ⨮ t))
    (let mv = seq 1 11 Game.ε)
    (let (C: c# T: t# R: r#) = count mv)
    -- r# = 82
    -- c# = 27
    -- t# = 27
  where

  -- open CountsSeq 1 11

  -- The move sequence mv ought to be executable.
  -- Prove from hyp
  hmv : ∃ λ rt → RMoves.rmoves kₐ kₜ mv rempty ≡ just rt
  hmv = {! hyp mv ε (move-sequence 1 11) !}

  -- Move count relation ship
  -- Prove lem with help of (thm-counts mv 0 ε) from hmv
  lem : c# * kₐ + t# * kₜ ≥ r#  -- 27 * (kₐ + kₜ) ≥ 82
  lem = {!c#!}

  thm-op : ¬(kₐ + kₜ ≤ 3)
  thm-op h = {!!}
    -- h implies  27 * (kₐ + kₜ) ≤ 81 which contradicts lem

  -- Prove from thm-op by decidability of ≤
  thm : kₐ + kₜ ≥ 4
  thm = {!!}
