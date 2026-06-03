{-# OPTIONS --safe #-}

open import Library
open import Data.Nat.Properties using (+-identityʳ; *-comm; ≤-refl; module ≤-Reasoning)
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

  -- Move count relation ship
  -- Prove lem with help of (thm-counts mv 0 ε) from hmv
  lem : c# * kₐ + t# * kₜ ≥ r#  -- 27 * (kₐ + kₜ) ≥ 82
  lem with hmv
  ... | leftover , run =
    begin
      r#
    ≤⟨ ≤-add-right r# leftover ⟩
      r# + leftover
    ≤⟨ thm-counts mv 0 ε run ⟩
      c# * kₐ + (t# * kₜ + 0)
    ≡⟨ cong (c# * kₐ +_) (+-identityʳ (t# * kₜ)) ⟩
      c# * kₐ + t# * kₜ
    ∎

  big : (kₐ + kₜ) * 27 ≥ 82
  big = begin
    82                ≤⟨ lem ⟩
    27 * kₐ + 27 * kₜ  ≡⟨ {!!} ⟩
    27 * (kₐ + kₜ)     ≡⟨ {!!} ⟩
    (kₐ + kₜ) * 27     ∎

  thm-op : kₐ + kₜ ≤ 3 → 82 ≤ 81
  thm-op h = begin
    82                ≤⟨ lem ⟩
    27 * kₐ + 27 * kₜ  ≡⟨ {!!} ⟩
    27 * (kₐ + kₜ)     ≤⟨ ? ⟩
    27 * 3            ∎

  foo : ∀ k → ¬ (k ≥ 4) → k ≤ 3
  foo 0 _ = refl
  foo 1 _ = refl
  foo 2 _ = refl
  foo 3 _ = refl
  foo (suc (suc (suc (suc k)))) h = h refl

  thm : kₐ + kₜ ≥ 4
  thm with 4 ≤? kₐ + kₜ
  thm | yes p = p
  thm | no ¬p with thm-op (foo (kₐ + kₜ) ¬p)
  ... | ()

{-
  thm' : ∀ k → k ≡ kₐ + kₜ → ¬(k ≤ 3)
  thm' zero eq rewrite eq with big
  ... | ()
  thm' (suc k) eq = {!!}



  thm' : ∀ k → k ≡ kₐ + kₜ → k ≥ 4
  thm' zero eq rewrite eq with big
  ... | ()
  thm' (suc k) eq = {!!}


  thm : kₐ + kₜ ≥ 4
  thm with kₐ + kₜ in eq
  ... | zero rewrite eq with big = ?
  ... | suc zero rewrite eq with big = ?
  ... | ()
  ... | suc (suc zero) rewrite eq with big
  ... | ()
  ... | suc (suc (suc zero)) rewrite eq with big
  ... | ()
  ... | suc (suc (suc (suc n))) = s≤s (s≤s (s≤s (s≤s z≤n)))



  sum27 : 27 * kₐ + 27 * kₜ ≡ (kₐ + kₜ) * 27
  sum27 =
    trans
      (cong (_+ (27 * kₜ)) (*-comm 27 kₐ))
      (trans
        (cong (kₐ * 27 +_) (*-comm 27 kₜ))
        (mul-sum kₐ kₜ 27))

  thm' : ∀ k → k ≡ kₐ + kₜ → k ≥ 4
  thm' zero eq = {!!}
  thm' (suc k) eq = {!!}

  thm : kₐ + kₜ ≥ 4
  thm = thm' (kₐ + kₜ) refl
-}

{-
  big : (kₐ + kₜ) * 27 ≥ 82
  big rewrite sum27 = ?

  big : (kₐ + kₜ) * 27 ≥ 82
  big rewrite thm-counts-seq 1 11 | sum27 = lem  -- OOM

  thm : kₐ + kₜ ≥ 4
  thm with kₐ + kₜ in eq
  ... | k = ?

  thm : kₐ + kₜ ≥ 4
  thm with kₐ + kₜ in eq
  ... | zero rewrite eq with big
  ... | ()
  ... | suc zero rewrite eq with big
  ... | ()
  ... | suc (suc zero) rewrite eq with big
  ... | ()
  ... | suc (suc (suc zero)) rewrite eq with big
  ... | ()
  ... | suc (suc (suc (suc n))) = s≤s (s≤s (s≤s (s≤s z≤n)))

  thm-op : ¬(kₐ + kₜ ≤ 3)
  thm-op h with kₐ + kₜ in eq
  ... | zero with thm
  ... | ()
  ... | suc zero with thm
  ... | ()
  ... | suc (suc zero) with thm
  ... | ()
  ... | suc (suc (suc zero)) with thm
  ... | ()
  ... | suc (suc (suc (suc n))) with h
  ... | ()
-- -}
