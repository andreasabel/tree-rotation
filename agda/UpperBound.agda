{-# OPTIONS --safe #-}

module UpperBound where

open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import Tree

open ≤-Reasoning

≤1+pred : ∀ n → n ≤ 1 + pred n
≤1+pred zero    = z≤n
≤1+pred (suc n) = ≤-refl

-- Φₗ sandwiched by Φᵣ:  Φᵣ ≤ Φₗ ≤ 1 + Φᵣ

Φᵣ≤Φₗ : ∀ t → Φᵣ t ≤ Φₗ t
Φᵣ≤Φₗ ε = z≤n
Φᵣ≤Φₗ (l ∙ r) = ⊔-lub
  (≤-trans
    (s≤s (Φᵣ≤Φₗ l))
    (m≤m⊔n (suc (Φₗ l)) (Φᵣ r)))
  (≤-trans
    pred[n]≤n
    (m≤n⊔m (suc (Φₗ l)) (Φᵣ r)))

Φₗ≤1+Φᵣ : ∀ t → Φₗ t ≤ 1 + Φᵣ t
Φₗ≤1+Φᵣ ε = z≤n
Φₗ≤1+Φᵣ (l ∙ r) = ⊔-lub
  (≤-trans
    (s≤s (Φₗ≤1+Φᵣ l))
    (+-monoʳ-≤ 1 (m≤m⊔n (suc (Φᵣ l)) (pred (Φᵣ r)))))
  (≤-trans
    (≤1+pred (Φᵣ r))
    (+-monoʳ-≤ 1 (m≤n⊔m (suc (Φᵣ l)) (pred (Φᵣ r)))))

-- Φ sandwiched by Φᵣ:  Φᵣ ≤ Φ ≤ 1 + Φᵣ

Φᵣ≤Φ : ∀ t → Φᵣ t ≤ Φ t
Φᵣ≤Φ ε = z≤n
Φᵣ≤Φ (l ∙ r) = ⊔-lub
  (≤-trans
    (s≤s (Φᵣ≤Φₗ l))
    (m≤m⊔n (suc (Φₗ l)) (pred (Φᵣ r))))
  (m≤n⊔m (suc (Φₗ l)) (pred (Φᵣ r)))

Φ≤1+Φᵣ : ∀ t → Φ t ≤ 1 + Φᵣ t
Φ≤1+Φᵣ ε = z≤n
Φ≤1+Φᵣ (l ∙ r) = ⊔-lub
  (≤-trans
    (s≤s (Φₗ≤1+Φᵣ l))
    (+-monoʳ-≤ 1 (m≤m⊔n (suc (Φᵣ l)) (pred (Φᵣ r)))))
  (≤-trans
    (m≤n⊔m (suc (Φᵣ l)) (pred (Φᵣ r)))
    (n≤1+n (suc (Φᵣ l) ⊔ pred (Φᵣ r))))

-- Φₗ bounded by Φ:  Φₗ ≤ 1+Φ

Φₗ≤1+Φ : ∀ t → Φₗ t ≤ 1 + Φ t
Φₗ≤1+Φ ε = z≤n
Φₗ≤1+Φ (l ∙ r) = ⊔-lub
  (≤-trans
    (m≤m⊔n (suc (Φₗ l)) (pred (Φᵣ r)))
    (n≤1+n (suc (Φₗ l) ⊔ pred (Φᵣ r))))
  (≤-trans
    (≤1+pred (Φᵣ r))
    (+-monoʳ-≤ 1 (m≤n⊔m (suc (Φₗ l)) (pred (Φᵣ r)))))

-- Amortization theorem: pay 3 for each append and tail, then the rotations are also paid for.

amor-append : 3 + Φ l + Φ r ≥ 1 + Φ (l ∙ r)
amor-append {l = l} {r = r} =
  begin
    1 + Φ (l ∙ r)
  ≤⟨ +-monoʳ-≤ 1 (m⊔n≤m+n (suc (Φₗ l)) (pred (Φᵣ r))) ⟩
    1 + (suc (Φₗ l) + pred (Φᵣ r))
  ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ (s≤s (Φₗ≤1+Φ l)) (≤-trans pred[n]≤n (Φᵣ≤Φ r))) ⟩
    1 + ((2 + Φ l) + Φ r)
  ≡⟨⟩
    3 + Φ l + Φ r
  ∎

amor-tail : tail t ≡ just t' → 3 + Φ t ≥ 1 + Φ t'
amor-tail {t = ε ∙ t} refl =
  begin
    1 + Φ t
  ≤⟨ +-monoʳ-≤ 1 (Φ≤1+Φᵣ t) ⟩
    2 + Φᵣ t
  ≤⟨ +-monoʳ-≤ 2 (≤1+pred (Φᵣ t)) ⟩
    3 + pred (Φᵣ t)
  ≤⟨ +-monoʳ-≤ 3 (m≤n⊔m 1 (pred (Φᵣ t))) ⟩
    3 + Φ (ε ∙ t)
  ∎

amor-rotate : rotate t ≡ just t' → Φ t ≥ 1 + Φ t'
amor-rotate {t = (t₁ ∙ t₂) ∙ t₃} refl = max-lemma (suc (Φₗ t₁)) (Φᵣ t₂) (Φᵣ t₃)
  where
  max-lemma : ∀ a b c → suc (a ⊔ pred (suc b ⊔ pred c)) ≤ suc (a ⊔ b) ⊔ pred c
  -- If c ∈ {0,1}, the term "⊔ pred c" vanishes and both sides become the same.
  max-lemma a b zero       = m≤m⊔n (suc (a ⊔ b)) 0
  max-lemma a b (suc zero) = m≤m⊔n (suc (a ⊔ b)) 0
  -- Otherwise, pred c ≡ suc c' and suc commutes with ⊔.
  max-lemma a b (suc (suc c)) rewrite sym (⊔-assoc a b c) = ≤-refl
