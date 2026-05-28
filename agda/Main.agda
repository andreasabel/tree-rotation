module Main where

open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Tree : Set where
  ε   : Tree
  _∙_ : (t₁ t₂ : Tree) → Tree

variable
  l r t t' t₁ t₂ : Tree

rotate : Tree → Maybe Tree
rotate ((t₁ ∙ t₂) ∙ t₃) = just (t₁ ∙ (t₂ ∙ t₃))
rotate _ = nothing

tail : Tree → Maybe Tree
tail (ε ∙ t) = just t
tail _       = nothing

Φᵣ : Tree → ℕ
Φᵣ ε = 0
Φᵣ (l ∙ r) = suc (Φᵣ l) ⊔ pred (Φᵣ r)

Φₗ : Tree → ℕ
Φₗ ε = 0
Φₗ (l ∙ r) = suc (Φₗ l) ⊔ Φᵣ r

Φ : Tree → ℕ
Φ ε = 0
Φ (l ∙ r) = suc (Φₗ l) ⊔ pred (Φᵣ r)

mutual
  kₐ : ℕ
  kₐ = {!!}

  kₜ : ℕ
  kₜ = {!!}

  amor-append : 1 + Φ l + Φ r ≤ kₐ + Φ (l ∙ r)
  amor-append {l = l} {r = r} = {!!}

  amor-tail : tail t ≡ just t' → 1 + Φ t ≤ kₜ + Φ t'
  amor-tail {t = t} eq = {!!}

  amor-rotate : rotate t ≡ just t' → 1 + Φ t ≤ Φ t'
  amor-rotate {t = t} eq = {!t!}
