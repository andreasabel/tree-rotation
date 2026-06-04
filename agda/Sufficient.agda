{-# OPTIONS --safe #-}

-- Potential function proves sufficiency of 2,2-budget

module Sufficient where

open import Library
open import Data.Nat.Properties using
  ( +-identityʳ; +-suc; +-assoc; +-comm
  ; ≤-refl; ≤-trans; ≤-pred; +-monoˡ-≤; +-monoʳ-≤; +-cancelʳ-≤; module ≤-Reasoning)

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import SingleTreeGame using (Moves; C; R; T; ε; _∙_; moves)

open import UpperBound using (amor-append; amor-tail; amor-rotate)
open import ResourcedSingleTreeGame

open ≤-Reasoning

open RMoves 2 2

-- Legal moves
-- n - n' ≤ Φ t - Φ t'  so  n + Φ t' ≤ n' + Φ t
-- What we have left (n') should at least be what we started with minus the potential diff.

Legal : Moves → RT → RT → Set
Legal m rt@(n ⨮ t) rt'@(n' ⨮ t')
  = rmoves m rt ≡ just rt'
  × n' + Φ t ≥ n + Φ t'

-- Goal is to prove this theorem by induction on the moves ms:

Thm-RMoves
  = ∀ (ms : Moves) (t t' : Tree) → moves ms t ≡ just t'
  → ∀ n → n ≥ Φ t
  → ∃ λ n' → (n' ≥ Φ t') × Legal ms (n ⨮ t) (n' ⨮ t')

-- These are the assumptions about Φ that are used in the proof:

append-budget : ∀ t → 2 + Φ t ≥ Φ (t ∙ ε)
append-budget t =
    subst (Φ (t ∙ ε) ≤_)
      (cong (2 +_) (+-identityʳ (Φ t)))
      (amor-append {l = t} {r = ε})

tail-budget : ∀ {t t'} → tail t ≡ just t' → 2 + Φ t ≥ Φ t'
tail-budget p = amor-tail p

rotate-budget : ∀ {t t'} → rotate t ≡ just t' → Φ t ≥ 1 + Φ t'
rotate-budget = amor-rotate

-- Theorem: legal move sequences are resource-correct.
-- Prove by induction on ms:
thm-rmoves : Thm-RMoves

-- Case move C
thm-rmoves C t .(t ∙ ε) refl n n≥Φt =
  2 + n , (
    ≤-trans
      (append-budget t)
      (+-monoʳ-≤ 2 n≥Φt)
  , ( refl
    , (begin
        n + Φ (t ∙ ε)
      ≤⟨ +-monoʳ-≤ n (append-budget t) ⟩
        n + (2 + Φ t)
      ≡⟨ sym (+-assoc n 2 (Φ t)) ⟩
        (n + 2) + Φ t
      ≡⟨ cong (_+ Φ t) (+-comm n 2) ⟩
        (2 + n) + Φ t
      ∎) ))

-- Case move T
thm-rmoves T (ε ∙ t') .t' refl n n≥Φt =
  2 + n , (
    ≤-trans
      (tail-budget {t = ε ∙ t'} {t' = t'} refl)
      (+-monoʳ-≤ 2 n≥Φt)
  , ( refl
    , (begin
        n + Φ t'
      ≤⟨ +-monoʳ-≤ n (tail-budget {t = ε ∙ t'} {t' = t'} refl) ⟩
        n + (2 + Φ (ε ∙ t'))
      ≡⟨ sym (+-assoc n 2 (Φ (ε ∙ t'))) ⟩
        (n + 2) + Φ (ε ∙ t')
      ≡⟨ cong (_+ Φ (ε ∙ t')) (+-comm n 2) ⟩
        (2 + n) + Φ (ε ∙ t')
      ∎) ))

-- Case move R
thm-rmoves R ((t₁ ∙ t₂) ∙ t₃) .(t₁ ∙ (t₂ ∙ t₃)) refl zero n≥Φt
  with ≤-trans (rotate-budget {t = (t₁ ∙ t₂) ∙ t₃} {t' = t₁ ∙ (t₂ ∙ t₃)} refl) n≥Φt
... | ()
thm-rmoves R ((t₁ ∙ t₂) ∙ t₃) .(t₁ ∙ (t₂ ∙ t₃)) refl (suc n) n≥Φt =
  n , (
    ≤-pred (≤-trans (rotate-budget {t = (t₁ ∙ t₂) ∙ t₃} {t' = t₁ ∙ (t₂ ∙ t₃)} refl) n≥Φt)
  , ( refl
    , (begin
        suc n + Φ (t₁ ∙ (t₂ ∙ t₃))
      ≡⟨ refl ⟩
        suc (n + Φ (t₁ ∙ (t₂ ∙ t₃)))
      ≡⟨ sym (+-suc n (Φ (t₁ ∙ (t₂ ∙ t₃)))) ⟩
        n + suc (Φ (t₁ ∙ (t₂ ∙ t₃)))
      ≤⟨ +-monoʳ-≤ n (rotate-budget {t = (t₁ ∙ t₂) ∙ t₃} {t' = t₁ ∙ (t₂ ∙ t₃)} refl) ⟩
        n + Φ ((t₁ ∙ t₂) ∙ t₃)
      ∎) ))

-- Case empty move sequence
thm-rmoves ε t .t refl n n≥Φt =
  n , (n≥Φt , (refl , ≤-refl))

-- Case move sequence concatenation
thm-rmoves (m ∙ m') t t' p n n≥Φt with moves m t in pm | p
... | nothing | ()
... | just u | p' with thm-rmoves m t u pm n n≥Φt
... | n₁ , (n₁≥Φu , (rm , legal₁)) with thm-rmoves m' u t' p' n₁ n₁≥Φu
... | n₂ , (n₂≥Φt' , (rm' , legal₂)) rewrite rm | rm' =
  n₂ , ( n₂≥Φt'
       , ( refl
         , compose-sum-inequalities {n = n} {n₁ = n₁} {n₂ = n₂} {a = Φ t} {b = Φ u} {c = Φ t'} legal₁ legal₂ ))
  where
    compose-sum-inequalities
      : ∀ {n n₁ n₂ a b c}
      → n₁ + a ≥ n + b
      → n₂ + b ≥ n₁ + c
      → n₂ + a ≥ n + c
    compose-sum-inequalities {n = n} {n₁} {n₂} {a} {b} {c} n₁+a≥n+b n₂+b≥n₁+c =
      let proof =
            begin
              (n + c) + b
            ≡⟨ +-assoc n c b ⟩
              n + (c + b)
            ≡⟨ cong (n +_) (+-comm c b) ⟩
              n + (b + c)
            ≡⟨ sym (+-assoc n b c) ⟩
              (n + b) + c
            ≤⟨ +-monoˡ-≤ c n₁+a≥n+b ⟩
              (n₁ + a) + c
            ≡⟨ +-assoc n₁ a c ⟩
              n₁ + (a + c)
            ≡⟨ cong (n₁ +_) (+-comm a c) ⟩
              n₁ + (c + a)
            ≡⟨ sym (+-assoc n₁ c a) ⟩
              (n₁ + c) + a
            ≤⟨ +-monoˡ-≤ a n₂+b≥n₁+c ⟩
              (n₂ + b) + a
            ≡⟨ +-assoc n₂ b a ⟩
              n₂ + (b + a)
            ≡⟨ cong (n₂ +_) (+-comm b a) ⟩
              n₂ + (a + b)
            ≡⟨ sym (+-assoc n₂ a b) ⟩
              (n₂ + a) + b
            ∎
      in +-cancelʳ-≤ b (n + c) (n₂ + a) proof
