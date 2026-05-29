{-# OPTIONS --safe #-}

module Counting where

open import Function using (id; _∘_)
open import Data.Maybe using (Maybe; nothing; just; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≥_)
open import Data.Nat.Properties using
  ( +-identityʳ; +-suc; +-assoc; +-comm
  ; ≤-refl; ≤-trans; ≤-pred; +-monoˡ-≤; +-monoʳ-≤; +-cancelʳ-≤; module ≤-Reasoning)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import Game using (Moves; C; R; T; ε; _∙_; moves)
open import Game using (_>=>_)

record MoveCounts : Set where
  constructor C:_T:_R:_
  field
    c# t# r# : ℕ

incC : MoveCounts → MoveCounts
incC (C: c# T: t# R: r#) = (C: suc c# T: t# R: r#)

incR : MoveCounts → MoveCounts
incR (C: c# T: t# R: r#) = (C: c# T: t# R: suc r#)

incT : MoveCounts → MoveCounts
incT (C: c# T: t# R: r#) = (C: c# T: suc t# R: r#)

counts : Moves → MoveCounts → MoveCounts
counts C = incC
counts T = incT
counts R = incR
counts ε = id
counts (m ∙ m₁) = counts m ∘ counts m₁

module CountsSeq (m n : ℕ) where
  c# = m * (2 + n) + 3 * m + 3      -- mn+3n+2m+3
  t# = c#
  r# = m * (4 * n + 3) + 3 * n + 2  -- 4mn+3n+3m+2

  Thm = ∀ m n → counts (seq m n ε) ≡ (C: c# T: c# R: r#)


-- TODO: Need lemmata concerning counts, following the structure of lemmata in Game.agda

thm-counts-seq : ∀ m n → CountsSeq.Thm m n
thm-counts-seq = ? -- TODO
