-- {-# OPTIONS --safe #-} -- activate when done

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≥_)

module ResourcedGame where -- (kₐ kₜ : ℕ) where

open import Function using (id; _∘_)
open import Data.Maybe
open import Data.Product using (∃; _×_)
open import Relation.Binary.PropositionalEquality

open import Tree using (Tree; ε; _∙_; tail; rotate; Φ)
open import Game

open import UpperBound using (amor-append; amor-tail; amor-rotate)

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
thm-rmoves = {!!}
