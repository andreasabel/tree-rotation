{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≥_)
open import Data.Nat.Properties

module ResourcedGame where -- (kₐ kₜ : ℕ) where

open import Function using (id; _∘_)
open import Data.Maybe
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import Game

open import UpperBound using (amor-append; amor-tail; amor-rotate)

open ≤-Reasoning

infixl 4  _⨮_
record Resourced (A : Set) : Set where
  constructor _⨮_  -- C-x 8 RET 2a2e
  field
    resources : ℕ
    payload   : A

rmap : {A : Set} → (ℕ → ℕ) → Resourced A → Resourced A
rmap f (n ⨮ a) = f n ⨮ a

RT = Resourced Tree

rtmap : {A : Set} → (ℕ → ℕ) → Maybe RT → Maybe RT
rtmap f nothing = nothing
rtmap f (just (n ⨮ a)) = just (f n ⨮ a)

rmoves : Moves → RT → Maybe RT
rmoves C (n     ⨮ t) = just (2 + n ⨮ t ∙ ε)
rmoves T (n     ⨮ t) = map (2 + n ⨮_) (tail t)
rmoves R (suc n ⨮ t) = map (n ⨮_) (rotate t)
rmoves R (zero  ⨮ t) = nothing
rmoves ε = just
rmoves (m ∙ m') = rmoves m >=> rmoves m'

-- Legal moves
-- n - n' ≤ Φ t - Φ t'  so  n + Φ t' ≤ n' + Φ t
-- What we have left (n') should at least be what we started with minus the potential diff.

Legal : Moves → RT → RT → Set
Legal m rt@(n ⨮ t) rt'@(n' ⨮ t')
  = rmoves m rt ≡ just rt'
  × n' + Φ t ≥ n + Φ t'

-- Prove by induction on ms:
thm-rmoves
  : ∀ (ms : Moves) (t t' : Tree) → moves ms t ≡ just t'
  → ∀ n → n ≥ Φ t
  → ∃ λ n' → (n' ≥ Φ t') × Legal ms (n ⨮ t) (n' ⨮ t')

compose-legal
  : ∀ {n n₁ n₂ a b c}
  → n₁ + a ≥ n + b
  → n₂ + b ≥ n₁ + c
  → n₂ + a ≥ n + c
compose-legal {n = n} {n₁} {n₂} {a} {b} {c} n₁+a≥n+b n₂+b≥n₁+c =
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

Φε≡0 : Φ ε ≡ 0
Φε≡0 = refl

Φ+ε≡Φ : ∀ t → Φ t + Φ ε ≡ Φ t
Φ+ε≡Φ t rewrite Φε≡0 = +-identityʳ (Φ t)

append-budget : ∀ t → 2 + Φ t ≥ Φ (t ∙ ε)
append-budget t =
  ≤-pred
    (subst (suc (Φ (t ∙ ε)) ≤_)
      (cong (3 +_) (Φ+ε≡Φ t))
      (amor-append {l = t} {r = ε}))

tail-budget : ∀ {t t'} → tail t ≡ just t' → 2 + Φ t ≥ Φ t'
tail-budget p = ≤-pred (amor-tail p)

rotate-budget : ∀ {t t'} → rotate t ≡ just t' → Φ t ≥ 1 + Φ t'
rotate-budget = amor-rotate

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

thm-rmoves ε t .t refl n n≥Φt =
  n , (n≥Φt , (refl , ≤-refl))

thm-rmoves (m ∙ m') t t' p n n≥Φt with moves m t in pm | p
... | nothing | ()
... | just u | p' with thm-rmoves m t u pm n n≥Φt
... | n₁ , (n₁≥Φu , (rm , legal₁)) with thm-rmoves m' u t' p' n₁ n₁≥Φu
... | n₂ , (n₂≥Φt' , (rm' , legal₂)) rewrite rm | rm' =
  n₂ , ( n₂≥Φt'
       , ( refl
         , compose-legal {n = n} {n₁ = n₁} {n₂ = n₂} {a = Φ t} {b = Φ u} {c = Φ t'} legal₁ legal₂ ))
