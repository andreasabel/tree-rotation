-- {-# OPTIONS --safe #-}  -- Turn this on once the proof is complete!

module Main where

open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import Tree

kₐ : ℕ
kₐ = {!!}

kₜ : ℕ
kₜ = {!!}

amor-append : kₐ + Φ l + Φ r ≥ 1 + Φ (l ∙ r)
amor-append {l = l} {r = r} = {!!}

amor-tail : tail t ≡ just t' → kₜ + Φ t ≥ 1 + Φ t'
amor-tail {t = ε ∙ t} refl = {!!}

amor-rotate : rotate t ≡ just t' → Φ t ≥ 1 + Φ t'
amor-rotate {t = (t₁ ∙ t₂) ∙ t₃} refl = {!!}
