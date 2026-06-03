{-# OPTIONS --safe #-}

-- Move execution with resource tracking

module ResourcedGame where

open import Library
open import Data.Nat.Properties using
  ( +-assoc; +-comm; +-identityʳ; *-distribʳ-+
  ; ≤-refl; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; module ≤-Reasoning)

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import Game using (Moves; C; R; T; ε; _∙_)
open import Counting using (count; counts; add; add-compose; C:_T:_R:_)

infixl 4  _⨮_
record Resourced (A : Set) : Set where
  constructor _⨮_  -- C-x 8 RET 2a2e
  field
    resources : ℕ
    payload   : A

RT = Resourced Tree

rempty : RT
rempty = 0 ⨮ ε

-- -- Updating the resources
-- rmap : {A : Set} → (ℕ → ℕ) → Resourced A → Resourced A
-- rmap f (n ⨮ a) = f n ⨮ a

-- rtmap : {A : Set} → (ℕ → ℕ) → Maybe RT → Maybe RT
-- rtmap f nothing = nothing
-- rtmap f (just (n ⨮ a)) = just (f n ⨮ a)

module RMoves (kₐ kₜ : ℕ) where

  rmoves : Moves → RT → Maybe RT
  rmoves C (n     ⨮ t) = just (kₐ + n ⨮ t ∙ ε)
  rmoves T (n     ⨮ t) = Maybe.map (kₜ + n ⨮_) (tail t)
  rmoves R (suc n ⨮ t) = Maybe.map (n ⨮_) (rotate t)
  rmoves R (zero  ⨮ t) = nothing
  rmoves ε = just
  rmoves (m ∙ m') = rmoves m >=> rmoves m'

  counts-add : ∀ m cs c t r → count m ≡ (C: c T: t R: r) → counts m cs ≡ add c t r cs
  counts-add C cs c t r refl = refl
  counts-add T cs c t r refl = refl
  counts-add R cs c t r refl = refl
  counts-add ε cs c t r refl = refl
  counts-add (m ∙ m') cs c t r eq
    with count m in cm | count m' in cm'
  ... | (C: c₁ T: t₁ R: r₁) | (C: c₂ T: t₂ R: r₂)
    with trans (sym eq) comp
    where
      comp : counts m (C: c₂ T: t₂ R: r₂) ≡ (C: (c₁ + c₂) T: (t₁ + t₂) R: (r₁ + r₂))
      comp = let open ≡-Reasoning in
        begin
          counts m (C: c₂ T: t₂ R: r₂)
        ≡⟨ counts-add m (C: c₂ T: t₂ R: r₂) c₁ t₁ r₁ cm ⟩
          add c₁ t₁ r₁ (C: c₂ T: t₂ R: r₂)
        ≡⟨ refl ⟩
          (C: (c₁ + c₂) T: (t₁ + t₂) R: (r₁ + r₂))
        ∎
  ... | refl
    rewrite counts-add m' cs c₂ t₂ r₂ cm'
          | counts-add m (add c₂ t₂ r₂ cs) c₁ t₁ r₁ cm
          | add-compose c₁ t₁ r₁ c₂ t₂ r₂ cs
    = refl

  count-compose
    : ∀ m m'
    → let (C: c₁ T: t₁ R: r₁) = count m ;
           (C: c₂ T: t₂ R: r₂) = count m'
       in count (m ∙ m') ≡ (C: (c₁ + c₂) T: (t₁ + t₂) R: (r₁ + r₂))
  count-compose m m' with count m in cm | count m' in cm'
  ... | (C: c₁ T: t₁ R: r₁) | (C: c₂ T: t₂ R: r₂) = let open ≡-Reasoning in
    begin
      counts m (C: c₂ T: t₂ R: r₂)
    ≡⟨ counts-add m (C: c₂ T: t₂ R: r₂) c₁ t₁ r₁ cm ⟩
      add c₁ t₁ r₁ (C: c₂ T: t₂ R: r₂)
    ≡⟨ refl ⟩
      (C: (c₁ + c₂) T: (t₁ + t₂) R: (r₁ + r₂))
    ∎

  counts-compose
    : ∀ m c₂ t₂ r₂
    → let (C: c₁ T: t₁ R: r₁) = count m
       in counts m (C: c₂ T: t₂ R: r₂) ≡ (C: (c₁ + c₂) T: (t₁ + t₂) R: (r₁ + r₂))
  counts-compose m c₂ t₂ r₂ with count m in cm
  ... | (C: c₁ T: t₁ R: r₁) = let open ≡-Reasoning in
    begin
      counts m (C: c₂ T: t₂ R: r₂)
    ≡⟨ counts-add m (C: c₂ T: t₂ R: r₂) c₁ t₁ r₁ cm ⟩
      add c₁ t₁ r₁ (C: c₂ T: t₂ R: r₂)
    ≡⟨ refl ⟩
      (C: (c₁ + c₂) T: (t₁ + t₂) R: (r₁ + r₂))
    ∎

  rhs-compose
    : ∀ c₁ t₁ c₂ t₂ n
    → c₂ * kₐ + (t₂ * kₜ + (c₁ * kₐ + (t₁ * kₜ + n)))
      ≡ (c₁ + c₂) * kₐ + ((t₁ + t₂) * kₜ + n)
  rhs-compose c₁ t₁ c₂ t₂ n = let open ≡-Reasoning in
    begin
      c₂ * kₐ + (t₂ * kₜ + (c₁ * kₐ + (t₁ * kₜ + n)))
    ≡⟨ cong (c₂ * kₐ +_) (sym (+-assoc (t₂ * kₜ) (c₁ * kₐ) (t₁ * kₜ + n))) ⟩
      c₂ * kₐ + ((t₂ * kₜ + c₁ * kₐ) + (t₁ * kₜ + n))
    ≡⟨ cong (λ k → c₂ * kₐ + (k + (t₁ * kₜ + n))) (+-comm (t₂ * kₜ) (c₁ * kₐ)) ⟩
      c₂ * kₐ + ((c₁ * kₐ + t₂ * kₜ) + (t₁ * kₜ + n))
    ≡⟨ sym (+-assoc (c₂ * kₐ) (c₁ * kₐ + t₂ * kₜ) (t₁ * kₜ + n)) ⟩
      (c₂ * kₐ + (c₁ * kₐ + t₂ * kₜ)) + (t₁ * kₜ + n)
    ≡⟨ cong (_+ (t₁ * kₜ + n)) (sym (+-assoc (c₂ * kₐ) (c₁ * kₐ) (t₂ * kₜ))) ⟩
      ((c₂ * kₐ + c₁ * kₐ) + t₂ * kₜ) + (t₁ * kₜ + n)
    ≡⟨ +-assoc (c₂ * kₐ + c₁ * kₐ) (t₂ * kₜ) (t₁ * kₜ + n) ⟩
      (c₂ * kₐ + c₁ * kₐ) + (t₂ * kₜ + (t₁ * kₜ + n))
    ≡⟨ cong ((c₂ * kₐ + c₁ * kₐ) +_) (sym (+-assoc (t₂ * kₜ) (t₁ * kₜ) n)) ⟩
      (c₂ * kₐ + c₁ * kₐ) + ((t₂ * kₜ + t₁ * kₜ) + n)
    ≡⟨ cong (λ k → k + ((t₂ * kₜ + t₁ * kₜ) + n)) (+-comm (c₂ * kₐ) (c₁ * kₐ)) ⟩
      (c₁ * kₐ + c₂ * kₐ) + ((t₂ * kₜ + t₁ * kₜ) + n)
    ≡⟨ cong (λ k → (c₁ * kₐ + c₂ * kₐ) + (k + n)) (+-comm (t₂ * kₜ) (t₁ * kₜ)) ⟩
      (c₁ * kₐ + c₂ * kₐ) + ((t₁ * kₜ + t₂ * kₜ) + n)
    ≡⟨ cong (λ k → k + ((t₁ * kₜ + t₂ * kₜ) + n)) (sym (*-distribʳ-+ kₐ c₁ c₂)) ⟩
      (c₁ + c₂) * kₐ + ((t₁ * kₜ + t₂ * kₜ) + n)
    ≡⟨ cong (λ k → (c₁ + c₂) * kₐ + (k + n)) (sym (*-distribʳ-+ kₜ t₁ t₂)) ⟩
      (c₁ + c₂) * kₐ + (((t₁ + t₂) * kₜ) + n)
    ∎

  -- The number of R moves is bounded by the number of C + T moves based on resources.

  thm-counts
    : ∀ m n t {n' t'} (let (C: c# T: t# R: r#) = count m)
    → rmoves m (n ⨮ t) ≡ just (n' ⨮ t')
    → r# + n' ≤ c# * kₐ + (t# * kₜ + n)
  thm-counts C n t refl rewrite +-identityʳ kₐ = ≤-refl
  thm-counts T n (ε ∙ t) refl rewrite +-identityʳ kₜ = ≤-refl
  thm-counts R (suc n) ((t₁ ∙ t₂) ∙ t₃) refl = ≤-refl
  thm-counts ε n t refl = ≤-refl
  thm-counts (m ∙ m') n t {n'} {t'} eq with rmoves m (n ⨮ t) in rm | eq
  ... | nothing | ()
  ... | just (n₁ ⨮ u) | eq' rewrite count-compose m m' =
    let
      p₁ = thm-counts m n t rm
      p₂ = thm-counts m' n₁ u eq'
      open ≤-Reasoning
    in
    begin
      (count m .Counting.MoveCounts.r# + count m' .Counting.MoveCounts.r#) + n'
    ≡⟨ +-assoc (count m .Counting.MoveCounts.r#) (count m' .Counting.MoveCounts.r#) n' ⟩
      count m .Counting.MoveCounts.r# + (count m' .Counting.MoveCounts.r# + n')
    ≤⟨ +-monoʳ-≤ (count m .Counting.MoveCounts.r#) p₂ ⟩
      count m .Counting.MoveCounts.r#
        + (count m' .Counting.MoveCounts.c# * kₐ + (count m' .Counting.MoveCounts.t# * kₜ + n₁))
    ≡⟨ sym (+-assoc (count m .Counting.MoveCounts.r#) (count m' .Counting.MoveCounts.c# * kₐ)
         (count m' .Counting.MoveCounts.t# * kₜ + n₁)) ⟩
      (count m .Counting.MoveCounts.r# + count m' .Counting.MoveCounts.c# * kₐ)
        + (count m' .Counting.MoveCounts.t# * kₜ + n₁)
    ≡⟨ cong (_+ (count m' .Counting.MoveCounts.t# * kₜ + n₁))
         (+-comm (count m .Counting.MoveCounts.r#) (count m' .Counting.MoveCounts.c# * kₐ)) ⟩
      (count m' .Counting.MoveCounts.c# * kₐ + count m .Counting.MoveCounts.r#)
        + (count m' .Counting.MoveCounts.t# * kₜ + n₁)
    ≡⟨ +-assoc (count m' .Counting.MoveCounts.c# * kₐ) (count m .Counting.MoveCounts.r#)
         (count m' .Counting.MoveCounts.t# * kₜ + n₁) ⟩
      count m' .Counting.MoveCounts.c# * kₐ
        + (count m .Counting.MoveCounts.r# + (count m' .Counting.MoveCounts.t# * kₜ + n₁))
    ≡⟨ cong (count m' .Counting.MoveCounts.c# * kₐ +_)
         (sym (+-assoc (count m .Counting.MoveCounts.r#) (count m' .Counting.MoveCounts.t# * kₜ) n₁)) ⟩
      count m' .Counting.MoveCounts.c# * kₐ
        + ((count m .Counting.MoveCounts.r# + count m' .Counting.MoveCounts.t# * kₜ) + n₁)
    ≡⟨ cong (λ k → count m' .Counting.MoveCounts.c# * kₐ + (k + n₁))
         (+-comm (count m .Counting.MoveCounts.r#) (count m' .Counting.MoveCounts.t# * kₜ)) ⟩
      count m' .Counting.MoveCounts.c# * kₐ
        + ((count m' .Counting.MoveCounts.t# * kₜ + count m .Counting.MoveCounts.r#) + n₁)
    ≡⟨ cong (count m' .Counting.MoveCounts.c# * kₐ +_)
         (+-assoc (count m' .Counting.MoveCounts.t# * kₜ) (count m .Counting.MoveCounts.r#) n₁) ⟩
      count m' .Counting.MoveCounts.c# * kₐ
        + (count m' .Counting.MoveCounts.t# * kₜ + (count m .Counting.MoveCounts.r# + n₁))
    ≤⟨ +-monoʳ-≤ (count m' .Counting.MoveCounts.c# * kₐ)
         (+-monoʳ-≤ (count m' .Counting.MoveCounts.t# * kₜ) p₁) ⟩
      count m' .Counting.MoveCounts.c# * kₐ
        + (count m' .Counting.MoveCounts.t# * kₜ
        + (count m .Counting.MoveCounts.c# * kₐ + (count m .Counting.MoveCounts.t# * kₜ + n)))
    ≡⟨ rhs-compose
         (count m .Counting.MoveCounts.c#)
         (count m .Counting.MoveCounts.t#)
         (count m' .Counting.MoveCounts.c#)
         (count m' .Counting.MoveCounts.t#)
         n ⟩
      (count m .Counting.MoveCounts.c# + count m' .Counting.MoveCounts.c#) * kₐ
        + ((count m .Counting.MoveCounts.t# + count m' .Counting.MoveCounts.t#) * kₜ + n)
    ∎
