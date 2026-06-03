{-# OPTIONS --safe #-}

module Sequence where

open import Library
open import Data.Nat.Properties using (+-suc; +-comm; +-identityʳ)

open import Tree using (Tree; ε; _∙_; tail; rotate)
open import Game

open ≡-Reasoning

cr : M
cr = c ∘ r

tr : M
tr = t ∘ r

crtr : M
crtr = c ∘ r ∘ t ∘ r

crtrr : M
crtrr = c ∘ r ∘ t ∘ r ∘ r

-- We are now constructing a move sequence (seq m n) that approximates the ratio
-- of R / C to 4 in the asymptotic case (m, n to infinity).

-- The starting sequence producing a right-spine.
start : ℕ → M
start n = c ∘ c ∘ r ∘ cr ^ n ∘ t ∘ r ^ n

-- A looping sequence returning to a right-spine.
loop : ℕ → M
loop n = cr ∘ crtrr ^ n ∘ crtr ∘ t ∘ r ^ n

-- A sequence unravelling a right-spine to the empty tree using
-- as many rotations as possible while only spending one C move.
unravel : ℕ → M
unravel n = cr ∘ tr ^ n ∘ (t ∘ t)

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

lem-cr-suf : ∀ n m ms → moves ((cr ^ n) ms) (ε ∙ left-spine m) ≡ moves ms (ε ∙ left-spine (n + m))
lem-cr-suf zero    m ms = refl
lem-cr-suf (suc n) m ms =
  subst (λ □ → moves ((cr ^ n) ms) (ε ∙ left-spine (suc m)) ≡ moves ms (ε ∙ left-spine □))
    (+-suc n m)
    (lem-cr-suf n (suc m) ms)

lem-rn-suf : ∀ n m ms → moves ((r ^ n) ms) (left-spine n ∙ right-spine m) ≡ moves ms (ε ∙ right-spine (n + m))
lem-rn-suf zero    m ms = refl
lem-rn-suf (suc n) m ms =
  subst (λ □ → moves ((r ^ n) ms) (left-spine n ∙ (ε ∙ right-spine m)) ≡ moves ms (ε ∙ right-spine □))
    (+-suc n m)
    (lem-rn-suf n (suc m) ms)

thm-trn-suf : ∀ n ms → moves (t ((r ^ n) ms)) (ε ∙ left-spine (1 + n)) ≡ moves ms (right-spine (1 + n))
thm-trn-suf n ms =
  subst
    (λ k → moves (t ((r ^ n) ms)) (ε ∙ left-spine (1 + n)) ≡ moves ms (ε ∙ right-spine k))
    (+-identityʳ n)
    (lem-rn-suf n 0 ms)

thm-start-suf : ∀ n ms → moves (start n ms) ε ≡ moves ms (right-spine (1 + n))
thm-start-suf n ms =
  begin
    moves (start n ms) ε
  ≡⟨ refl ⟩
    moves ((cr ^ n) (t ((r ^ n) ms))) (ε ∙ left-spine 1)
  ≡⟨ lem-cr-suf n 1 (t ((r ^ n) ms)) ⟩
    moves (t ((r ^ n) ms)) (ε ∙ left-spine (n + 1))
  ≡⟨ subst
       (λ k → moves (t ((r ^ n) ms)) (ε ∙ left-spine k) ≡ moves ms (right-spine (1 + n)))
       (+-comm 1 n)
       (thm-trn-suf n ms) ⟩
    moves ms (right-spine (1 + n))
  ∎

-- ccr(cr)ⁿtrⁿ produces a right-spine when started on the empty tree
-- The theorem follows from lemmata thm-ccrcrn and thm-trn
thm-start : ∀ n → move (start n) ε ≡ just (right-spine (1 + n))
thm-start n = thm-start-suf n ε

-- Part 2: legality and cyclicity of (loop n)

lem-crtrr1 : ∀{n m} → moves ((((C ∙ R) ∙ T) ∙ R) ∙ R) (ε ∙ (right-spine (suc n) ∙ left-spine m))
  ≡ just (ε ∙ (right-spine n ∙ left-spine (suc m)))
lem-crtrr1 = refl

lem-crtrr : ∀ n m l → move ((c ∘ r ∘ t ∘ r ∘ r) ^ n) (ε ∙ (right-spine (n + m) ∙ left-spine l))
  ≡ just (ε ∙ (right-spine m ∙ left-spine (n + l)))
lem-crtrr zero m l = refl
lem-crtrr (suc n) m l =
  subst
    (λ k → move ((c ∘ r ∘ t ∘ r ∘ r) ^ n) (ε ∙ (right-spine (n + m) ∙ left-spine (suc l)))
         ≡ just (ε ∙ (right-spine m ∙ left-spine k)))
    (+-suc n l)
    (lem-crtrr n m (suc l))

lem-crtr : ∀{m} → moves (((C ∙ R) ∙ T) ∙ R) (ε ∙ (ε ∙ left-spine m))
  ≡ just (ε ∙ left-spine (suc m))
lem-crtr = refl

lem-cr-suf-right : ∀ n ms → moves (cr ms) (right-spine (1 + n)) ≡ moves ms (ε ∙ (right-spine n ∙ ε))
lem-cr-suf-right n ms = refl

lem-crtrr-suf : ∀ n m l ms → moves ((crtrr ^ n) ms) (ε ∙ (right-spine (n + m) ∙ left-spine l))
  ≡ moves ms (ε ∙ (right-spine m ∙ left-spine (n + l)))
lem-crtrr-suf zero    m l ms = refl
lem-crtrr-suf (suc n) m l ms =
  subst
    (λ k → moves ((crtrr ^ n) ms) (ε ∙ (right-spine (n + m) ∙ left-spine (suc l)))
         ≡ moves ms (ε ∙ (right-spine m ∙ left-spine k)))
    (+-suc n l)
    (lem-crtrr-suf n m (suc l) ms)

lem-crtr-suf : ∀ m ms → moves (crtr ms) (ε ∙ (ε ∙ left-spine m)) ≡ moves ms (ε ∙ left-spine (suc m))
lem-crtr-suf m ms = refl

thm-loop-suf : ∀ n ms → moves (loop n ms) (right-spine (1 + n)) ≡ moves ms (right-spine (1 + n))
thm-loop-suf n ms =
  begin
    moves (loop n ms) (right-spine (1 + n))
  ≡⟨ lem-cr-suf-right n ((crtrr ^ n) (crtr (t ((r ^ n) ms)))) ⟩
    moves ((crtrr ^ n) (crtr (t ((r ^ n) ms)))) (ε ∙ (right-spine n ∙ ε))
  ≡⟨ subst
       (λ k → moves ((crtrr ^ n) (crtr (t ((r ^ n) ms)))) (ε ∙ (right-spine k ∙ ε))
            ≡ moves (crtr (t ((r ^ n) ms))) (ε ∙ (ε ∙ left-spine (n + 0))))
       (+-identityʳ n)
       (lem-crtrr-suf n 0 0 (crtr (t ((r ^ n) ms)))) ⟩
    moves (crtr (t ((r ^ n) ms))) (ε ∙ (ε ∙ left-spine (n + 0)))
  ≡⟨ subst
       (λ k → moves (crtr (t ((r ^ n) ms))) (ε ∙ (ε ∙ left-spine k))
            ≡ moves (t ((r ^ n) ms)) (ε ∙ left-spine (suc n)))
       (sym (+-identityʳ n))
       (lem-crtr-suf n (t ((r ^ n) ms))) ⟩
    moves (t ((r ^ n) ms)) (ε ∙ left-spine (suc n))
  ≡⟨ thm-trn-suf n ms ⟩
    moves ms (right-spine (1 + n))
  ∎

-- Like thm-start, this theorem needs intermediate lemmata
-- since loop has two sections that are repeated n times.
thm-loop : ∀ n → move (loop n) (right-spine (1 + n)) ≡ just (right-spine (1 + n))
thm-loop n = thm-loop-suf n ε

thm-loop-m-suf : ∀ m n ms → moves (((loop n) ^ m) ms) (right-spine (1 + n)) ≡ moves ms (right-spine (1 + n))
thm-loop-m-suf zero    n ms = refl
thm-loop-m-suf (suc m) n ms =
  begin
    moves (((loop n) ^ suc m) ms) (right-spine (1 + n))
  ≡⟨ thm-loop-suf n (((loop n) ^ m) ms) ⟩
    moves (((loop n) ^ m) ms) (right-spine (1 + n))
  ≡⟨ thm-loop-m-suf m n ms ⟩
    moves ms (right-spine (1 + n))
  ∎

-- The loop can be iterated.
thm-loop-m : ∀ m n → move ((loop n) ^ m) (right-spine (1 + n)) ≡ just (right-spine (1 + n))
thm-loop-m m n = thm-loop-m-suf m n ε

-- Part 3: legality of (unravel n)

lem-trr1 : ∀{n} → moves (T ∙ R) (ε ∙ (right-spine (suc n) ∙ ε))
  ≡ just (ε ∙ (right-spine n ∙ ε))
lem-trr1 = refl

lem-trr : ∀ n m → move ((t ∘ r) ^ n) (ε ∙ (right-spine (n + m) ∙ ε))
  ≡ just (ε ∙ (right-spine m ∙ ε))
lem-trr zero    m = refl
lem-trr (suc n) m = lem-trr n m

lem-tr-suf : ∀ n m ms → moves ((tr ^ n) ms) (ε ∙ (right-spine (n + m) ∙ ε))
  ≡ moves ms (ε ∙ (right-spine m ∙ ε))
lem-tr-suf zero    m ms = refl
lem-tr-suf (suc n) m ms = lem-tr-suf n m ms

thm-unravel-suf : ∀ n ms → moves (unravel n ms) (right-spine (1 + n)) ≡ moves ms ε
thm-unravel-suf n ms =
  begin
    moves (unravel n ms) (right-spine (1 + n))
  ≡⟨ lem-cr-suf-right n ((tr ^ n) (t (t ms))) ⟩
    moves ((tr ^ n) (t (t ms))) (ε ∙ (right-spine n ∙ ε))
  ≡⟨ subst
       (λ k → moves ((tr ^ n) (t (t ms))) (ε ∙ (right-spine k ∙ ε))
            ≡ moves (t (t ms)) (ε ∙ (ε ∙ ε)))
       (+-identityʳ n)
       (lem-tr-suf n 0 (t (t ms))) ⟩
    moves (t (t ms)) (ε ∙ (ε ∙ ε))
  ≡⟨ refl ⟩
    moves ms ε
  ∎

-- This theorem also needs intermediate lemmata.
thm-unravel : ∀ n → move (unravel n) (right-spine (1 + n)) ≡ just ε
thm-unravel n = thm-unravel-suf n ε

-- Summary: legality of (seq m n)

-- Executing the sequence for any m and n succeeds and transforms the empty tree back to the empty tree.
-- This theorem is a consequence of thm-start, thm-loop, and thm-unravel.
thm-seq : ∀ m n → move (seq m n) ε ≡ just ε
thm-seq m n =
  begin
    move (seq m n) ε
  ≡⟨ thm-start-suf n (((loop n) ^ m) (unravel n ε)) ⟩
    moves (((loop n) ^ m) (unravel n ε)) (right-spine (1 + n))
  ≡⟨ thm-loop-m-suf m n (unravel n ε) ⟩
    move (unravel n) (right-spine (1 + n))
  ≡⟨ thm-unravel n ⟩
    just ε
  ∎
