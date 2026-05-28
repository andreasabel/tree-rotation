{-# OPTIONS --safe #-}

module Main where

open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Tree
open import UpperBound using (amor-append; amor-tail; amor-rotate)

-- Amortization theorem: pay 3 for each append and tail, then the rotations are also paid for.

kₐ : ℕ
kₐ = 3

kₜ : ℕ
kₜ = 3

amortization
  : (                     kₐ + Φ t + Φ t' ≥ 1 + Φ (t ∙ t'))
  × (tail t   ≡ just t' → kₜ + Φ t        ≥ 1 + Φ t')
  × (rotate t ≡ just t' → Φ t             ≥ 1 + Φ t')

amortization {t = t} {t' = t'} =
  amor-append {l = t} {r = t'} , amor-tail , amor-rotate
