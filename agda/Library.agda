{-# OPTIONS --safe #-}

module Library where

open import Function            public using (id; _∘_)
open import Data.Empty          public using (⊥; ⊥-elim)
open import Data.Fin            public using (Fin; zero; suc)
open import Data.List           public using (List; []; _∷_)
open import Data.Maybe          public using (Maybe; nothing; just; _>>=_) hiding (module Maybe)
open import Data.Nat            public using (ℕ; zero; suc; pred) hiding (module ℕ)
open import Data.Product        public using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec            public using (Vec; []; _∷_; replicate)
open import Relation.Nullary    public using (¬_; yes; no)

open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

module Maybe = Data.Maybe

_>=>_ : {A B C : Set} → (A → Maybe B) → (B → Maybe C) → A → Maybe C
f >=> g = λ a → f a >>= g

module ℕ where

  open import Data.Nat public
    using
    (_+_; _*_; _⊔_
    ; _≤_; _≥_; _<_; _≮_; z≤n; s≤s
    )
  open import Data.Nat.Properties public
    -- using
    -- ( +-identityʳ; +-assoc; +-comm; *-distribʳ-+; +-suc; *-suc
    -- ; ≤-refl; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; _≤?_; module ≤-Reasoning
    -- )
  open import Data.Nat.Solver public
  open import Data.Nat.Tactic.RingSolver public using (solve-∀)

  infixr 10 _^_

  _^_ : {A : Set} → (A → A) → ℕ → A → A
  f ^ zero = id
  f ^ suc n = f ∘ (f ^ n)

  -- Retract

  ≤1+pred : ∀ n → n ≤ suc (pred n)
  ≤1+pred zero    = z≤n
  ≤1+pred (suc n) = ≤-refl

-- Variables

variable
  k l m n : ℕ
