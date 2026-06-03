{-# OPTIONS --safe #-}

open import Library
open import Data.Nat.Properties using
  ( +-identityʳ; *-comm
  ;  *-monoˡ-≤ ; *-monoʳ-≤; ≤-refl; *-distribˡ-+; *-distribʳ-+; m≤n+m; <-irrefl; module ≤-Reasoning)
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

  open RMoves kₐ kₜ
  open ≤-Reasoning

  ≤-add-right : ∀ a b → a ≤ a + b
  ≤-add-right zero    b = z≤n
  ≤-add-right (suc a) b = s≤s (≤-add-right a b)

  -- open CountsSeq 1 11

  -- The move sequence mv ought to be executable.
  -- Prove from hyp
  hmv : ∃ λ leftover → RMoves.rmoves kₐ kₜ mv rempty ≡ just (leftover ⨮ ε)
  hmv = hyp mv ε (thm-seq 1 11)

  counts-seq-1-11 : kₐ * c# + kₜ * t# ≥ r#  -- (kₐ + kₜ) * 27 ≥ 82
  counts-seq-1-11 with hmv
  ... | leftover , run =
    begin
      r#
    ≤⟨ m≤n+m r# leftover ⟩
      leftover + r#
    ≤⟨ thm-counts' mv 0 ε run ⟩
       kₐ * c# + kₜ * t#
    ∎

  thm-op : kₐ + kₜ ≤ 3 → 82 ≤ 81
  thm-op h = begin
    82                ≤⟨ counts-seq-1-11 ⟩
    kₐ * 27 + kₜ * 27  ≡⟨ sym (*-distribʳ-+ 27 kₐ kₜ) ⟩
    (kₐ + kₜ) * 27     ≤⟨ *-monoˡ-≤ 27 h ⟩
    3 * 27            ∎

  foo : ∀ k → ¬ (k ≥ 4) → k ≤ 3
  foo 0 _ = z≤n
  foo 1 _ = s≤s z≤n
  foo 2 _ = s≤s (s≤s z≤n)
  foo 3 _ = ≤-refl
  foo (suc (suc (suc (suc k)))) h with h (s≤s (s≤s (s≤s (s≤s z≤n))))
  ... | ()

  thm-op' : ¬(kₐ + kₜ ≤ 3)
  thm-op' h = <-irrefl refl (thm-op h)

  thm : kₐ + kₜ ≥ 4
  thm with 4 ≤? kₐ + kₜ
  thm | yes p = p
  thm | no ¬p = ⊥-elim (thm-op' (foo (kₐ + kₜ) ¬p))

{- OOM
  thm-op' : ¬(kₐ + kₜ ≤ 3)
  thm-op' h with thm-op h
  ... |
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s ())
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
-}

{-
  thm : kₐ + kₜ ≥ 4
  thm with 4 ≤? kₐ + kₜ
  thm | yes p = p
  thm | no ¬p with thm-op (foo (kₐ + kₜ) ¬p)
  ... |
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
   (s≤s ())
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))
   ))))))))))

  -- big : (kₐ + kₜ) * 27 ≥ 82
  -- big = begin
  --   82                ≤⟨ lem ⟩
  --   27 * kₐ + 27 * kₜ  ≡⟨ {!!} ⟩
  --   27 * (kₐ + kₜ)     ≡⟨ {!!} ⟩
  --   (kₐ + kₜ) * 27     ∎

-- -}
