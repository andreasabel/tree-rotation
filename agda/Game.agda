{-# OPTIONS --safe #-}

module Game where

open import Function using (id; _∘_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Tree using (Tree; ε; _∙_; tail; rotate)

-- General tools

_>=>_ : {A B C : Set} → (A → Maybe B) → (B → Maybe C) → A → Maybe C
f >=> g = λ a → f a >>= g

infixr 10 _^_

_^_ : {A : Set} → (A → A) → ℕ → A → A
f ^ zero = id
f ^ suc n = f ∘ (f ^ n)

-- Degenerate tree, left leaning.

left-spine : ℕ → Tree
left-spine zero    = ε
left-spine (suc n) = left-spine n ∙ ε

-- Degenerate tree, right leaning.

right-spine : ℕ → Tree
right-spine zero    = ε
right-spine (suc n) = ε ∙ right-spine n

-- The tree game, with three possible moves C (concat), T (tail) and R (rotate)
-- to manipulate a single tree.

data Moves : Set where
  C T R : Moves
  ε     : Moves
  _∙_   : (m m' : Moves) → Moves

-- Running a move sequence.
-- Not every sequence is executable since T and R are not always available.

moves : Moves → Tree → Maybe Tree
moves C t = just (t ∙ ε)
moves T = tail
moves R = rotate
moves ε = just
moves (m ∙ m') = moves m >=> moves m'

-- The Cayley form of the Moves monoid, useful for definition repetitions.

M = Moves → Moves

move : M → Tree → Maybe Tree
move f = moves (f ε)

c : M
c m = C ∙ m

t : M
t m = T ∙ m

r : M
r m = R ∙ m

-- We are now constructing a move sequence (seq m n) that approximates the ratio
-- of R / C to 4 in the asymptotic case (m, n to infinity).

-- The starting sequence producing a right-spine.
start : ℕ → M
start n = c ∘ c ∘ r ∘ (c ∘ r) ^ n ∘ t ∘ r ^ n

-- A looping sequence returning to a right-spine.
loop : ℕ → M
loop n = (c ∘ r) ∘ (c ∘ r ∘ t ∘ r ∘ r) ^ n ∘ (c ∘ r ∘ t ∘ r) ∘ t ∘ r ^ n

-- A sequence unravelling a right-spine to the empty tree using
-- as many rotations as possible while only spending one C move.
unravel : ℕ → M
unravel n = (c ∘ r) ∘ (t ∘ r) ^ n ∘ (t ∘ t)

-- The whole tree move sequence.
seq : (m n : ℕ) → M
seq m n = (start n) ∘ (loop n) ^ m ∘ (unravel n)

-- The following theorems establish that (seq m n) is a legal move sequence
-- from the empty tree back to the empty tree.

-- Part 1: legality of (start n)

lem-cr1 : ∀{n} → moves (C ∙ R) (ε ∙ left-spine n) ≡ just (ε ∙ left-spine (suc n))
lem-cr1 = refl

lem-cr : ∀ n m → move ((c ∘ r) ^ n) (ε ∙ left-spine m) ≡ just (ε ∙ left-spine (n + m))
lem-cr zero m = refl
lem-cr (suc n) m =
  subst (λ □ → move ((c ∘ r) ^ n) (ε ∙ left-spine (suc m)) ≡ just (ε ∙ left-spine □))
    (+-suc n m)
    (lem-cr n (suc m))

ccrcrn : ℕ → M
ccrcrn n = c ∘ c ∘ r ∘ (c ∘ r) ^ n

thm-ccrcrn : ∀ n → move (ccrcrn n) ε ≡ just (ε ∙ left-spine (n + 1))
thm-ccrcrn n = lem-cr n 1

lem-rn : ∀ n m → move (r ^ n) (left-spine n ∙ right-spine m) ≡ just (ε ∙ right-spine (n + m))
lem-rn zero m = refl
lem-rn (suc n) m =
  subst (λ □ → moves (((λ mv → R ∙ mv) ^ n) ε) (left-spine n ∙ (ε ∙ right-spine m)) ≡ just (ε ∙ right-spine □))
    (+-suc n m)
    (lem-rn n (suc m))

thm-trn : ∀ n → move (t ∘ r ^ n) (ε ∙ left-spine (1 + n)) ≡ just (right-spine (1 + n + 0))
thm-trn n = lem-rn n 0

-- ccr(cr)ⁿtrⁿ produces a right-spine when started on the empty tree
-- The theorem follows from lemmata thm-ccrcrn and thm-trn
thm-start : ∀ n → move (start n) ε ≡ just (right-spine (1 + n))
thm-start n = {!!}

-- Part 2: legality and cyclicity of (loop n)

-- Like thm-start, this theorem needs intermediate lemmata
-- since loop has two sections that are repeated n times.
thm-loop : ∀ n → move (loop n) (right-spine (1 + n)) ≡ just (right-spine (1 + n))
thm-loop = {!!}

-- The loop can be iterated.
thm-loop-m : ∀ m n → move ((loop n) ^ m) (right-spine (1 + n)) ≡ just (right-spine (1 + n))
thm-loop-m = {!!}

-- Part 3: legality of (unravel n)

-- This theorem also needs intermediate lemmata.
thm-unravel : ∀ n → move (unravel n) (right-spine (1 + n)) ≡ just ε
thm-unravel n = {!!}

-- Summary: legality of (seq m n)

-- Executing the sequence for any m and n succeeds and transforms the empty tree back to the empty tree.
-- This theorem is a consequence of thm-start, thm-loop, and thm-unravel.
thm-seq : ∀ m n → move (seq m n) ε ≡ just ε
thm-seq m n = {!!}
