{-# OPTIONS --safe #-}

module Counting where

open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_)
open import Data.Nat.Properties using
  ( +-identityʳ; +-suc; +-assoc; +-comm; *-suc
  ; module ≤-Reasoning)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Game using (Moves; C; R; T; ε; _∙_; _^_; cr; tr; crtrr; start; loop; unravel; seq)

open ≡-Reasoning

record MoveCounts : Set where
  constructor C:_T:_R:_
  field
    c# t# r# : ℕ

incC : MoveCounts → MoveCounts
incC (C: c# T: t# R: r#) = (C: suc c# T: t# R: r#)

incR : MoveCounts → MoveCounts
incR (C: c# T: t# R: r#) = (C: c# T: t# R: suc r#)

incT : MoveCounts → MoveCounts
incT (C: c# T: t# R: r#) = (C: c# T: suc t# R: r#)

counts : Moves → MoveCounts → MoveCounts
counts C = incC
counts T = incT
counts R = incR
counts ε = id
counts (m ∙ m₁) = counts m ∘ counts m₁

zero-counts : MoveCounts
zero-counts = C: 0 T: 0 R: 0

add : ℕ → ℕ → ℕ → MoveCounts → MoveCounts
add c t r (C: c# T: t# R: r#) = C: (c + c#) T: (t + t#) R: (r + r#)

add-zero : ∀ c t r → add c t r zero-counts ≡ C: c T: t R: r
add-zero c t r rewrite +-identityʳ c | +-identityʳ t | +-identityʳ r = refl

add-compose : ∀ a t r a' t' r' cs → add a t r (add a' t' r' cs) ≡ add (a + a') (t + t') (r + r') cs
add-compose a t r a' t' r' (C: c# T: t#₀ R: r#₀)
  rewrite sym (+-assoc a a' c#)
        | sym (+-assoc t t' t#₀)
        | sym (+-assoc r r' r#₀)
  = refl

lem-cr-suf : ∀ n ms cs → counts ((cr ^ n) ms) cs ≡ add n 0 n (counts ms cs)
lem-cr-suf zero    ms cs = refl
lem-cr-suf (suc n) ms cs =
  begin
    counts ((cr ^ suc n) ms) cs
  ≡⟨ refl ⟩
    add 1 0 1 (counts ((cr ^ n) ms) cs)
  ≡⟨ cong (add 1 0 1) (lem-cr-suf n ms cs) ⟩
    add 1 0 1 (add n 0 n (counts ms cs))
  ≡⟨ add-compose 1 0 1 n 0 n (counts ms cs) ⟩
    add (1 + n) 0 (1 + n) (counts ms cs)
  ≡⟨ refl ⟩
    add (suc n) 0 (suc n) (counts ms cs)
  ∎

lem-r-suf : ∀ n ms cs → counts ((Game.r ^ n) ms) cs ≡ add 0 0 n (counts ms cs)
lem-r-suf zero    ms cs = refl
lem-r-suf (suc n) ms cs =
  begin
    counts ((Game.r ^ suc n) ms) cs
  ≡⟨ refl ⟩
    add 0 0 1 (counts ((Game.r ^ n) ms) cs)
  ≡⟨ cong (add 0 0 1) (lem-r-suf n ms cs) ⟩
    add 0 0 1 (add 0 0 n (counts ms cs))
  ≡⟨ add-compose 0 0 1 0 0 n (counts ms cs) ⟩
    add 0 0 (1 + n) (counts ms cs)
  ≡⟨ refl ⟩
    add 0 0 (suc n) (counts ms cs)
  ∎

lem-crtrr-r : ∀ n → 3 + 3 * n ≡ 3 * suc n
lem-crtrr-r n = sym (*-suc 3 n)

lem-crtrr-suf : ∀ n ms cs → counts ((crtrr ^ n) ms) cs ≡ add n n (3 * n) (counts ms cs)
lem-crtrr-suf zero    ms cs = refl
lem-crtrr-suf (suc n) ms cs =
  begin
    counts ((crtrr ^ suc n) ms) cs
  ≡⟨ refl ⟩
    add 1 1 3 (counts ((crtrr ^ n) ms) cs)
  ≡⟨ cong (add 1 1 3) (lem-crtrr-suf n ms cs) ⟩
    add 1 1 3 (add n n (3 * n) (counts ms cs))
  ≡⟨ add-compose 1 1 3 n n (3 * n) (counts ms cs) ⟩
    add (1 + n) (1 + n) (3 + 3 * n) (counts ms cs)
  ≡⟨ cong (λ k → add (1 + n) (1 + n) k (counts ms cs)) (lem-crtrr-r n) ⟩
    add (1 + n) (1 + n) (3 * suc n) (counts ms cs)
  ≡⟨ refl ⟩
    add (suc n) (suc n) (3 * suc n) (counts ms cs)
  ∎

lem-tr-suf : ∀ n ms cs → counts ((tr ^ n) ms) cs ≡ add 0 n n (counts ms cs)
lem-tr-suf zero    ms cs = refl
lem-tr-suf (suc n) ms cs =
  begin
    counts ((tr ^ suc n) ms) cs
  ≡⟨ refl ⟩
    add 0 1 1 (counts ((tr ^ n) ms) cs)
  ≡⟨ cong (add 0 1 1) (lem-tr-suf n ms cs) ⟩
    add 0 1 1 (add 0 n n (counts ms cs))
  ≡⟨ add-compose 0 1 1 0 n n (counts ms cs) ⟩
    add 0 (1 + n) (1 + n) (counts ms cs)
  ≡⟨ refl ⟩
    add 0 (suc n) (suc n) (counts ms cs)
  ∎

lem-loop-r : ∀ n → 3 * n + (n + 3) ≡ 4 * n + 3
lem-loop-r n =
  begin
    3 * n + (n + 3)
  ≡⟨ sym (+-assoc (3 * n) n 3) ⟩
    (3 * n + n) + 3
  ≡⟨ cong (_+ 3) (+-comm (3 * n) n) ⟩
    (n + 3 * n) + 3
  ≡⟨ refl ⟩
    4 * n + 3
  ∎

lem-crtr-suf : ∀ ms cs → counts (Game.crtr ms) cs ≡ add 1 1 2 (counts ms cs)
lem-crtr-suf ms cs = refl

lem-one-mul : ∀ n → 1 * n ≡ n
lem-one-mul n = +-identityʳ n

lem-two-mul : ∀ n → 2 * n ≡ n + n
lem-two-mul n =
  begin
    2 * n
  ≡⟨ refl ⟩
    n + 1 * n
  ≡⟨ cong (n +_) (lem-one-mul n) ⟩
    n + n
  ∎

lem-mul-step : ∀ m k → k + m * k ≡ suc m * k
lem-mul-step m k = refl

lem-start-suf : ∀ n ms cs → counts (start n ms) cs ≡ add (n + 2) 1 ((n + n) + 1) (counts ms cs)
lem-start-suf n ms cs =
  begin
    counts (start n ms) cs
  ≡⟨ refl ⟩
    add 2 0 1 (counts ((cr ^ n) (T ∙ ((Game.r ^ n) ms)) ) cs)
  ≡⟨ cong (add 2 0 1) (lem-cr-suf n (T ∙ ((Game.r ^ n) ms)) cs) ⟩
    add 2 0 1 (add n 0 n (counts (T ∙ ((Game.r ^ n) ms)) cs))
  ≡⟨ cong (add 2 0 1) refl ⟩
    add 2 0 1 (add n 0 n (add 0 1 0 (counts ((Game.r ^ n) ms) cs)))
  ≡⟨ cong (add 2 0 1) (add-compose n 0 n 0 1 0 (counts ((Game.r ^ n) ms) cs)) ⟩
    add 2 0 1 (add (n + 0) 1 (n + 0) (counts ((Game.r ^ n) ms) cs))
  ≡⟨ cong (add 2 0 1)
       (cong (λ k → add k 1 (n + 0) (counts ((Game.r ^ n) ms) cs)) (+-identityʳ n)) ⟩
    add 2 0 1 (add n 1 (n + 0) (counts ((Game.r ^ n) ms) cs))
  ≡⟨ cong (add 2 0 1)
       (cong (λ k → add n 1 k (counts ((Game.r ^ n) ms) cs)) (+-identityʳ n)) ⟩
    add 2 0 1 (add n 1 n (counts ((Game.r ^ n) ms) cs))
  ≡⟨ cong (add 2 0 1) (cong (add n 1 n) (lem-r-suf n ms cs)) ⟩
    add 2 0 1 (add n 1 n (add 0 0 n (counts ms cs)))
  ≡⟨ cong (add 2 0 1) (add-compose n 1 n 0 0 n (counts ms cs)) ⟩
    add 2 0 1 (add (n + 0) 1 (n + n) (counts ms cs))
  ≡⟨ cong (add 2 0 1) (cong (λ k → add k 1 (n + n) (counts ms cs)) (+-identityʳ n)) ⟩
    add 2 0 1 (add n 1 (n + n) (counts ms cs))
  ≡⟨ add-compose 2 0 1 n 1 (n + n) (counts ms cs) ⟩
    add (2 + n) 1 (1 + (n + n)) (counts ms cs)
  ≡⟨ cong (λ k → add k 1 (1 + (n + n)) (counts ms cs)) (+-comm 2 n) ⟩
    add (n + 2) 1 (1 + (n + n)) (counts ms cs)
  ≡⟨ cong (λ k → add (n + 2) 1 k (counts ms cs)) (+-comm 1 (n + n)) ⟩
    add (n + 2) 1 ((n + n) + 1) (counts ms cs)
  ∎

lem-loop-suf : ∀ n ms cs → counts (loop n ms) cs ≡ add (n + 2) (n + 2) (4 * n + 3) (counts ms cs)
lem-loop-suf n ms cs =
  begin
    counts (loop n ms) cs
  ≡⟨ refl ⟩
    add 1 0 1 (counts ((crtrr ^ n) (Game.crtr (T ∙ ((Game.r ^ n) ms))) ) cs)
  ≡⟨ cong (add 1 0 1) (lem-crtrr-suf n (Game.crtr (T ∙ ((Game.r ^ n) ms))) cs) ⟩
    add 1 0 1 (add n n (3 * n) (counts (Game.crtr (T ∙ ((Game.r ^ n) ms))) cs))
  ≡⟨ cong (add 1 0 1) (cong (add n n (3 * n)) (lem-crtr-suf (T ∙ ((Game.r ^ n) ms)) cs)) ⟩
    add 1 0 1 (add n n (3 * n) (add 1 1 2 (counts (T ∙ ((Game.r ^ n) ms)) cs)))
  ≡⟨ cong (add 1 0 1) (cong (add n n (3 * n)) refl) ⟩
    add 1 0 1 (add n n (3 * n) (add 1 1 2 (add 0 1 0 (counts ((Game.r ^ n) ms) cs))))
  ≡⟨ cong (add 1 0 1) (cong (add n n (3 * n)) (add-compose 1 1 2 0 1 0 (counts ((Game.r ^ n) ms) cs))) ⟩
    add 1 0 1 (add n n (3 * n) (add 1 2 2 (counts ((Game.r ^ n) ms) cs)))
  ≡⟨ cong (add 1 0 1) (cong (add n n (3 * n) ∘ add 1 2 2) (lem-r-suf n ms cs)) ⟩
    add 1 0 1 (add n n (3 * n) (add 1 2 2 (add 0 0 n (counts ms cs))))
  ≡⟨ cong (add 1 0 1) (cong (add n n (3 * n)) (add-compose 1 2 2 0 0 n (counts ms cs))) ⟩
    add 1 0 1 (add n n (3 * n) (add 1 2 (2 + n) (counts ms cs)))
  ≡⟨ cong (add 1 0 1)
       (cong (add n n (3 * n)) (cong (λ k → add 1 2 k (counts ms cs)) (+-comm 2 n))) ⟩
    add 1 0 1 (add n n (3 * n) (add 1 2 (n + 2) (counts ms cs)))
  ≡⟨ cong (add 1 0 1) (add-compose n n (3 * n) 1 2 (n + 2) (counts ms cs)) ⟩
    add 1 0 1 (add (n + 1) (n + 2) (3 * n + (n + 2)) (counts ms cs))
  ≡⟨ add-compose 1 0 1 (n + 1) (n + 2) (3 * n + (n + 2)) (counts ms cs) ⟩
    add (1 + (n + 1)) (n + 2) (1 + (3 * n + (n + 2))) (counts ms cs)
  ≡⟨ cong (λ k → add (1 + (n + 1)) (n + 2) k (counts ms cs))
       (begin
          1 + (3 * n + (n + 2))
        ≡⟨ refl ⟩
          suc (3 * n + (n + 2))
        ≡⟨ sym (+-suc (3 * n) (n + 2)) ⟩
          3 * n + suc (n + 2)
        ≡⟨ cong (3 * n +_) (sym (+-suc n 2)) ⟩
          3 * n + (n + 3)
        ≡⟨ lem-loop-r n ⟩
          4 * n + 3
        ∎) ⟩
    add (1 + (n + 1)) (n + 2) (4 * n + 3) (counts ms cs)
  ≡⟨ cong (λ k → add k (n + 2) (4 * n + 3) (counts ms cs))
       (begin
          1 + (n + 1)
        ≡⟨ cong (1 +_) (+-comm n 1) ⟩
          2 + n
        ≡⟨ +-comm 2 n ⟩
          n + 2
        ∎) ⟩
    add (n + 2) (n + 2) (4 * n + 3) (counts ms cs)
  ∎

lem-loop-m-suf : ∀ m n ms cs → counts (((loop n) ^ m) ms) cs ≡ add (m * (n + 2)) (m * (n + 2)) (m * (4 * n + 3)) (counts ms cs)
lem-loop-m-suf zero    n ms cs = refl
lem-loop-m-suf (suc m) n ms cs =
  begin
    counts (((loop n) ^ suc m) ms) cs
  ≡⟨ lem-loop-suf n (((loop n) ^ m) ms) cs ⟩
    add (n + 2) (n + 2) (4 * n + 3) (counts (((loop n) ^ m) ms) cs)
  ≡⟨ cong (add (n + 2) (n + 2) (4 * n + 3)) (lem-loop-m-suf m n ms cs) ⟩
    add (n + 2) (n + 2) (4 * n + 3) (add (m * (n + 2)) (m * (n + 2)) (m * (4 * n + 3)) (counts ms cs))
  ≡⟨ add-compose (n + 2) (n + 2) (4 * n + 3) (m * (n + 2)) (m * (n + 2)) (m * (4 * n + 3)) (counts ms cs) ⟩
    add ((n + 2) + m * (n + 2)) ((n + 2) + m * (n + 2)) ((4 * n + 3) + m * (4 * n + 3)) (counts ms cs)
  ≡⟨ cong (λ k → add k ((n + 2) + m * (n + 2)) ((4 * n + 3) + m * (4 * n + 3)) (counts ms cs)) (lem-mul-step m (n + 2)) ⟩
    add (suc m * (n + 2)) ((n + 2) + m * (n + 2)) ((4 * n + 3) + m * (4 * n + 3)) (counts ms cs)
  ≡⟨ cong (λ k → add (suc m * (n + 2)) k ((4 * n + 3) + m * (4 * n + 3)) (counts ms cs)) (lem-mul-step m (n + 2)) ⟩
    add (suc m * (n + 2)) (suc m * (n + 2)) ((4 * n + 3) + m * (4 * n + 3)) (counts ms cs)
  ≡⟨ cong (λ k → add (suc m * (n + 2)) (suc m * (n + 2)) k (counts ms cs)) (lem-mul-step m (4 * n + 3)) ⟩
    add (suc m * (n + 2)) (suc m * (n + 2)) (suc m * (4 * n + 3)) (counts ms cs)
  ∎

lem-unravel-suf : ∀ n ms cs → counts (unravel n ms) cs ≡ add 1 (n + 2) (n + 1) (counts ms cs)
lem-unravel-suf n ms cs =
  begin
    counts (unravel n ms) cs
  ≡⟨ refl ⟩
    add 1 0 1 (counts ((tr ^ n) (T ∙ (T ∙ ms))) cs)
  ≡⟨ cong (add 1 0 1) (lem-tr-suf n (T ∙ (T ∙ ms)) cs) ⟩
    add 1 0 1 (add 0 n n (counts (T ∙ (T ∙ ms)) cs))
  ≡⟨ cong (add 1 0 1) refl ⟩
    add 1 0 1 (add 0 n n (add 0 2 0 (counts ms cs)))
  ≡⟨ cong (add 1 0 1) (add-compose 0 n n 0 2 0 (counts ms cs)) ⟩
    add 1 0 1 (add 0 (n + 2) (n + 0) (counts ms cs))
  ≡⟨ cong (add 1 0 1)
       (cong (λ k → add 0 (n + 2) k (counts ms cs)) (+-identityʳ n)) ⟩
    add 1 0 1 (add 0 (n + 2) n (counts ms cs))
  ≡⟨ add-compose 1 0 1 0 (n + 2) n (counts ms cs) ⟩
    add 1 (n + 2) (1 + n) (counts ms cs)
  ≡⟨ cong (λ k → add 1 (n + 2) k (counts ms cs)) (+-comm 1 n) ⟩
    add 1 (n + 2) (n + 1) (counts ms cs)
  ∎

module CountsSeq (m n : ℕ) where
  c# = m * (n + 2) + n + 3
  t# = c#
  r# = m * (4 * n + 3) + 3 * n + 2

  Thm = counts (seq m n ε) zero-counts ≡ (C: c# T: c# R: r#)


ct-total : ∀ m n → (n + 2) + (m * (n + 2) + 1) ≡ m * (n + 2) + n + 3
ct-total m n =
  begin
    (n + 2) + (m * (n + 2) + 1)
  ≡⟨ sym (+-assoc (n + 2) (m * (n + 2)) 1) ⟩
    ((n + 2) + m * (n + 2)) + 1
  ≡⟨ cong (_+ 1) (+-comm (n + 2) (m * (n + 2))) ⟩
    (m * (n + 2) + (n + 2)) + 1
  ≡⟨ +-assoc (m * (n + 2)) (n + 2) 1 ⟩
    m * (n + 2) + ((n + 2) + 1)
  ≡⟨ cong (m * (n + 2) +_) (begin
        (n + 2) + 1
      ≡⟨ +-assoc n 2 1 ⟩
        n + (2 + 1)
      ≡⟨ refl ⟩
        n + 3
      ∎) ⟩
    m * (n + 2) + (n + 3)
  ≡⟨ sym (+-assoc (m * (n + 2)) n 3) ⟩
    m * (n + 2) + n + 3
  ∎

r-total : ∀ m n → ((n + n) + 1) + (m * (4 * n + 3) + (n + 1)) ≡ m * (4 * n + 3) + 3 * n + 2
r-total m n =
  begin
    ((n + n) + 1) + (m * (4 * n + 3) + (n + 1))
  ≡⟨ sym (+-assoc ((n + n) + 1) (m * (4 * n + 3)) (n + 1)) ⟩
    (((n + n) + 1) + m * (4 * n + 3)) + (n + 1)
  ≡⟨ cong (_+ (n + 1)) (+-comm ((n + n) + 1) (m * (4 * n + 3))) ⟩
    (m * (4 * n + 3) + ((n + n) + 1)) + (n + 1)
  ≡⟨ +-assoc (m * (4 * n + 3)) ((n + n) + 1) (n + 1) ⟩
    m * (4 * n + 3) + (((n + n) + 1) + (n + 1))
  ≡⟨ cong (m * (4 * n + 3) +_) (begin
        ((n + n) + 1) + (n + 1)
  ≡⟨ +-assoc (n + n) 1 (n + 1) ⟩
        (n + n) + (1 + (n + 1))
      ≡⟨ cong ((n + n) +_) (begin
           1 + (n + 1)
         ≡⟨ cong (1 +_) (+-comm n 1) ⟩
           2 + n
         ≡⟨ +-comm 2 n ⟩
           n + 2
         ∎) ⟩
        (n + n) + (n + 2)
      ≡⟨ +-assoc n n (n + 2) ⟩
        n + (n + (n + 2))
      ≡⟨ cong (n +_) (sym (+-assoc n n 2)) ⟩
        n + ((n + n) + 2)
      ≡⟨ sym (+-assoc n (n + n) 2) ⟩
        (n + (n + n)) + 2
      ≡⟨ cong (_+ 2) (begin
           n + (n + n)
         ≡⟨ cong (n +_) (sym (lem-two-mul n)) ⟩
           n + 2 * n
         ≡⟨ lem-mul-step 2 n ⟩
           3 * n
         ∎) ⟩
        3 * n + 2
      ∎) ⟩
    m * (4 * n + 3) + (3 * n + 2)
  ≡⟨ sym (+-assoc (m * (4 * n + 3)) (3 * n) 2) ⟩
    m * (4 * n + 3) + 3 * n + 2
  ∎

thm-counts-seq : ∀ m n → CountsSeq.Thm m n
thm-counts-seq m n =
  begin
    counts (seq m n ε) zero-counts
  ≡⟨ lem-start-suf n (((loop n) ^ m) (unravel n ε)) zero-counts ⟩
    add (n + 2) 1 ((n + n) + 1) (counts (((loop n) ^ m) (unravel n ε)) zero-counts)
  ≡⟨ cong (add (n + 2) 1 ((n + n) + 1)) (lem-loop-m-suf m n (unravel n ε) zero-counts) ⟩
    add (n + 2) 1 ((n + n) + 1)
      (add (m * (n + 2)) (m * (n + 2)) (m * (4 * n + 3)) (counts (unravel n ε) zero-counts))
  ≡⟨ cong (add (n + 2) 1 ((n + n) + 1))
       (cong (add (m * (n + 2)) (m * (n + 2)) (m * (4 * n + 3))) (lem-unravel-suf n ε zero-counts)) ⟩
    add (n + 2) 1 ((n + n) + 1)
      (add (m * (n + 2)) (m * (n + 2)) (m * (4 * n + 3)) (add 1 (n + 2) (n + 1) zero-counts))
  ≡⟨ cong (add (n + 2) 1 ((n + n) + 1))
       (add-compose (m * (n + 2)) (m * (n + 2)) (m * (4 * n + 3)) 1 (n + 2) (n + 1) zero-counts) ⟩
    add (n + 2) 1 ((n + n) + 1)
      (add (m * (n + 2) + 1) (m * (n + 2) + (n + 2)) (m * (4 * n + 3) + (n + 1)) zero-counts)
  ≡⟨ add-compose (n + 2) 1 ((n + n) + 1) (m * (n + 2) + 1) (m * (n + 2) + (n + 2)) (m * (4 * n + 3) + (n + 1)) zero-counts ⟩
    add ((n + 2) + (m * (n + 2) + 1))
        (1 + (m * (n + 2) + (n + 2)))
        (((n + n) + 1) + (m * (4 * n + 3) + (n + 1)))
        zero-counts
  ≡⟨ cong (λ k → add k (1 + (m * (n + 2) + (n + 2))) (((n + n) + 1) + (m * (4 * n + 3) + (n + 1))) zero-counts)
       (ct-total m n) ⟩
    add (m * (n + 2) + n + 3)
        (1 + (m * (n + 2) + (n + 2)))
        (((n + n) + 1) + (m * (4 * n + 3) + (n + 1)))
        zero-counts
  ≡⟨ cong (λ k → add (m * (n + 2) + n + 3) k (((n + n) + 1) + (m * (4 * n + 3) + (n + 1))) zero-counts)
       (begin
          1 + (m * (n + 2) + (n + 2))
        ≡⟨ refl ⟩
          suc (m * (n + 2) + (n + 2))
        ≡⟨ cong suc (+-comm (m * (n + 2)) (n + 2)) ⟩
          suc ((n + 2) + m * (n + 2))
       ≡⟨ sym (+-suc (n + 2) (m * (n + 2))) ⟩
         (n + 2) + suc (m * (n + 2))
       ≡⟨ cong ((n + 2) +_) (cong suc (sym (+-identityʳ (m * (n + 2))))) ⟩
         (n + 2) + suc (m * (n + 2) + 0)
       ≡⟨ cong ((n + 2) +_) (sym (+-suc (m * (n + 2)) 0)) ⟩
         (n + 2) + (m * (n + 2) + 1)
       ≡⟨ ct-total m n ⟩
         m * (n + 2) + n + 3
       ∎) ⟩
    add (m * (n + 2) + n + 3)
        (m * (n + 2) + n + 3)
        (((n + n) + 1) + (m * (4 * n + 3) + (n + 1)))
        zero-counts
  ≡⟨ cong (λ k → add (m * (n + 2) + n + 3) (m * (n + 2) + n + 3) k zero-counts)
       (r-total m n) ⟩
    add (m * (n + 2) + n + 3)
        (m * (n + 2) + n + 3)
        (m * (4 * n + 3) + 3 * n + 2)
        zero-counts
  ≡⟨ add-zero (m * (n + 2) + n + 3) (m * (n + 2) + n + 3) (m * (4 * n + 3) + 3 * n + 2) ⟩
    (C: (m * (n + 2) + n + 3) T: (m * (n + 2) + n + 3) R: (m * (4 * n + 3) + 3 * n + 2))
  ∎
