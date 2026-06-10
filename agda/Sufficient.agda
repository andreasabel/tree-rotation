{-# OPTIONS --safe #-}

-- Potential function proves sufficiency of 2,2-budget

module Sufficient where

open import Library
open import Tree using (Tree; ε; _∙_; tail; rotate; _⨮_; module Potential)

open import UpperBound using (amor-append; amor-tail; amor-rotate)
open import MultiTreeGame using (Forest; Moves; U; C; R; T; ε; _∙_; run; RF; module RMoves; Φs; pick; concat)

open ℕ
open Potential
open ≤-Reasoning

open RMoves 2 2

-- Legal moves
-- n - n' ≤ Φ t - Φ t'  so  n + Φ t' ≤ n' + Φ t
-- What we have left (n') should at least be what we started with minus the potential diff.

Legal : Moves m n → RF m → RF n → Set
Legal mv rf@(k ⨮ ts) rf'@(k' ⨮ ts')
  = rmoves mv rf ≡ just rf'
  × k' + Φs ts ≥ k + Φs ts'

-- Goal is to prove this theorem by induction on the moves ms:

Thm-RMoves
  = ∀ {m n} (mv : Moves m n) (ts : Forest m) (ts' : Forest n)
  → run mv ts ≡ just ts'
  → ∀ k → k ≥ Φs ts
  → ∃ λ k' → (k' ≥ Φs ts') × Legal mv (k ⨮ ts) (k' ⨮ ts')

append-budget : ∀ t₁ t₂ → 2 + Φ t₁ + Φ t₂ ≥ Φ (t₁ ∙ t₂)
append-budget t₁ t₂ = amor-append {l = t₁} {r = t₂}

tail-budget : ∀ {t t'} → tail t ≡ just t' → 2 + Φ t ≥ Φ t'
tail-budget p = amor-tail p

rotate-budget : ∀ {t t'} → rotate t ≡ just t' → Φ t ≥ 1 + Φ t'
rotate-budget = amor-rotate

pick-view : ∀ {n} (i : Fin n) (ts : Forest n)
  → ∃ λ m → ∃ λ (eq : n ≡ suc m) → ∃ λ t → ∃ λ (ts' : Forest m) →
      pick i ts ≡ (m , eq , t , ts') × Φs ts ≡ Φ t + Φs ts'
pick-view zero (t ∷ ts) = _ , refl , t , ts , (refl , refl)
pick-view (suc i) (h ∷ ts) with pick i ts in pi | pick-view i ts
... | _ , refl , t , ts' | _ , refl , .t , .ts' , refl , pΦ =
  _ , refl , t , (h ∷ ts') , (
    refl
  , trans
      (cong (Φ h +_) pΦ)
      (trans
        (sym (+-assoc (Φ h) (Φ t) (Φs ts')))
        (trans
          (cong (_+ Φs ts') (+-comm (Φ h) (Φ t)))
          (+-assoc (Φ t) (Φ h) (Φs ts')))))

pick-Φ : ∀ {n m} (i : Fin n) (ts : Forest n) {eq : n ≡ suc m} {t : Tree} {ts' : Forest m}
       → pick i ts ≡ (m , eq , t , ts')
       → Φs ts ≡ Φ t + Φs ts'
pick-Φ i ts pk with pick-view i ts
... | _ , refl , _ , _ , pk' , pΦ with trans (sym pk) pk'
... | refl = pΦ

concat-budget : ∀ {m} (i : Fin (1 + m)) (j : Fin m) (ts : Forest (1 + m)) → 2 + Φs ts ≥ Φs (concat i j ts)
concat-budget i j ts with pick i ts in pk₁
... | _ , refl , t₁ , ts₁ with pick j ts₁ in pk₂
... | _ , refl , t₂ , ts₂ =
  begin
    Φ (t₁ ∙ t₂) + Φs ts₂
  ≤⟨ +-monoˡ-≤ (Φs ts₂) (append-budget t₁ t₂) ⟩
    (2 + Φ t₁ + Φ t₂) + Φs ts₂
  ≡⟨ +-assoc 2 (Φ t₁ + Φ t₂) (Φs ts₂) ⟩
    2 + ((Φ t₁ + Φ t₂) + Φs ts₂)
  ≡⟨ cong (2 +_) (+-assoc (Φ t₁) (Φ t₂) (Φs ts₂)) ⟩
    2 + (Φ t₁ + (Φ t₂ + Φs ts₂))
  ≡⟨ cong (2 +_) (sym (cong (Φ t₁ +_) (pick-Φ j ts₁ pk₂))) ⟩
    2 + (Φ t₁ + Φs ts₁)
  ≡⟨ cong (2 +_) (sym (pick-Φ i ts pk₁)) ⟩
    2 + Φs ts
  ∎

rotate-budget-forest : ∀ {m} (i : Fin m) (ts : Forest m) {ts' : Forest m}
  → run (R i) ts ≡ just ts'
  → Φs ts ≥ 1 + Φs ts'
rotate-budget-forest i ts {ts'} p with pick-view i ts
... | _ , refl , t , ts₁ , pk , pΦ rewrite pk with rotate t in pr | p
... | nothing | ()
... | just t' | refl =
  begin
    1 + Φs ts'
  ≡⟨ refl ⟩
    1 + (Φ t' + Φs ts₁)
  ≡⟨ sym (+-assoc 1 (Φ t') (Φs ts₁)) ⟩
    (1 + Φ t') + Φs ts₁
  ≤⟨ +-monoˡ-≤ (Φs ts₁) (rotate-budget pr) ⟩
    Φ t + Φs ts₁
  ≡⟨ sym pΦ ⟩
    Φs ts
  ∎

-- Theorem: legal move sequences are resource-correct.
-- Prove by induction on mv:
thm-rmoves : Thm-RMoves

thm-rmoves U ts .(ε ∷ ts) refl k k≥Φs =
  k , (k≥Φs , (refl , ≤-refl))

thm-rmoves (C i j) ts .(concat i j ts) refl k k≥Φs =
  2 + k , (
    ≤-trans
      (concat-budget i j ts)
      (+-monoʳ-≤ 2 k≥Φs)
  , ( refl
    , (begin
        k + Φs (concat i j ts)
      ≤⟨ +-monoʳ-≤ k (concat-budget i j ts) ⟩
        k + (2 + Φs ts)
      ≡⟨ sym (+-assoc k 2 (Φs ts)) ⟩
        (k + 2) + Φs ts
      ≡⟨ cong (_+ Φs ts) (+-comm k 2) ⟩
        (2 + k) + Φs ts
      ∎) ))

thm-rmoves (T i) ts ts' p k k≥Φs with pick i ts in pk-i
... | _ , refl , t , ts₁ with tail t in pt | p
... | nothing | ()
... | just t' | refl =
  2 + k , (
    ≤-trans tail-bound (+-monoʳ-≤ 2 k≥Φs)
  , ( refl
    , (begin
        k + (Φ t' + Φs ts₁)
      ≤⟨ +-monoʳ-≤ k tail-bound ⟩
        k + (2 + Φs ts)
      ≡⟨ sym (+-assoc k 2 (Φs ts)) ⟩
        (k + 2) + Φs ts
      ≡⟨ cong (_+ Φs ts) (+-comm k 2) ⟩
        (2 + k) + Φs ts
      ∎) ))
  where
    tail-bound : Φ t' + Φs ts₁ ≤ 2 + Φs ts
    tail-bound = begin
        Φ t' + Φs ts₁
      ≤⟨ +-monoˡ-≤ (Φs ts₁) (tail-budget pt) ⟩
        (2 + Φ t) + Φs ts₁
      ≡⟨ +-assoc 2 (Φ t) (Φs ts₁) ⟩
        2 + (Φ t + Φs ts₁)
      ≡⟨ cong (2 +_) (sym (pick-Φ i ts pk-i)) ⟩
        2 + Φs ts
      ∎

thm-rmoves (R i) ts ts' p zero k≥Φs with ≤-trans (rotate-budget-forest i ts p) k≥Φs
... | ()
thm-rmoves (R i) ts ts' p (suc k) k≥Φs with pick i ts in pk-i
... | _ , refl , t , ts₁ with rotate t in pr | p
... | nothing | ()
... | just t' | refl =
  k , (
    ≤-pred (≤-trans rot-bound k≥Φs)
  , ( refl
    , (begin
        suc k + (Φ t' + Φs ts₁)
      ≡⟨ sym (+-suc k (Φ t' + Φs ts₁)) ⟩
        k + suc (Φ t' + Φs ts₁)
      ≤⟨ +-monoʳ-≤ k rot-bound ⟩
        k + Φs ts
      ∎) ))
  where
    rot-bound : 1 + (Φ t' + Φs ts₁) ≤ Φs ts
    rot-bound = begin
        1 + (Φ t' + Φs ts₁)
      ≡⟨ sym (+-assoc 1 (Φ t') (Φs ts₁)) ⟩
        (1 + Φ t') + Φs ts₁
      ≤⟨ +-monoˡ-≤ (Φs ts₁) (rotate-budget pr) ⟩
        Φ t + Φs ts₁
      ≡⟨ sym (pick-Φ i ts pk-i) ⟩
        Φs ts
      ∎

thm-rmoves ε ts .ts refl k k≥Φs =
  k , (k≥Φs , (refl , ≤-refl))

thm-rmoves (mv ∙ mv') ts ts' p k k≥Φs with run mv ts in pm | p
... | nothing | ()
... | just us | p' with thm-rmoves mv ts us pm k k≥Φs
... | k₁ , (k₁≥Φus , (rm , legal₁)) with thm-rmoves mv' us ts' p' k₁ k₁≥Φus
... | k₂ , (k₂≥Φts' , (rm' , legal₂)) rewrite rm | rm' =
  k₂ , ( k₂≥Φts'
       , ( refl
         , compose-sum-inequalities {n = k} {n₁ = k₁} {n₂ = k₂}
             {a = Φs ts} {b = Φs us} {c = Φs ts'} legal₁ legal₂ ))
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
