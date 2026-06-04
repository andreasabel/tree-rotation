-- The budget kₐ + kₜ approximates 4.
-- This means for all 0 < ε < 1 we get kₐ + kₜ + ε ≥ 4.
-- It is sufficient to show that for all N > 0 we show that there is such ε = p/q ≤ 1/N.
-- So, given N we have to find p and q such that Np ≤ q and (kₐ + kₜ)q + p ≥ 4q.
-- With our sequence we get e.g.  kₐ + kₜ ≥ 4 - (14m+10)/(m²+5m+3)  so
-- kₐ + kₜ + (14m+10)/(m²+5m+3) ≥ 4 or
-- (kₐ + kₜ)(m²+5m+3) + (14m+10) ≥ 4(m²+5m+3).
-- Picking q = m²+5m+3 and p = 14m+10 we have to show that Np ≤ q meaning (14m+10)N ≤ m²+5m+3.
-- This gives  m²+(5-14N)m+(3-10N) ≥ 0.
-- The positive root is ½(14N - 5 + √2(14N-5)² + 4(10N-3))) =
-- Guess: m ≥ 14N
-- Testing:
-- (14N)² + 14N(5-14N) - 10N + 3 =
-- (14N)² + 70N - (14N)² - 10N + 3 =
-- 60N + 3 ≥ 0
-- More generally,  (MN)²+MN(5-14N)+(3-10N) ≥ 0.
-- (MN)²+MN(5-14N)+(3-10N) =
-- MMN² - 14MN² + 5MN + 3 - 10N =
-- (M-14)MN² + (5M-10)N + 3 ≥ 0
-- So M ≥ 14N.

-- Given N, with p = 196N + 10 and q = 196N² + 70N + 3 we have Np ≤ q
-- and (kₐ + kₜ)q + p ≥ 4q thanks to our sequence for m=n=14N.

open import Library
open import Tree using (ε)
open import SingleTreeGame using (Moves; ε; moves)
open import Sequence using (seq; thm-seq)
open import ResourcedSingleTreeGame using (_⨮_; rempty; module RMoves)
open import Counting using (MoveCounts; count; C:_T:_R:_; thm-counts-seq)

open import Data.Nat.Properties using
  ( +-assoc; +-comm; +-identityʳ; *-distribʳ-+
  ; ≤-refl; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; m≤n+m; module ≤-Reasoning)
import Data.Nat.Solver as Nat
import Data.Nat.Tactic.RingSolver as Nat

module Approx
  -- Budget for concat and tail.
  (kₐ kₜ : ℕ)
  -- We assume that this budget is sufficient to execute any legal move sequence.
  (hyp : ∀ mv t
   → moves mv ε ≡ just t
   → ∃ λ leftover → RMoves.rmoves kₐ kₜ mv rempty ≡ just (leftover ⨮ t))
  -- Approximation precision as N goes to +∞.
  (N : ℕ)
  where

open ≤-Reasoning

≤-add-right : ∀ a b → a ≤ a + b
≤-add-right zero    b = z≤n
≤-add-right (suc a) b = s≤s (≤-add-right a b)

p : ℕ
p = N * 196 + 10

q : ℕ
q = N * N * 196 + N * 70 + 3

-- We are showing these two theorems:

Fraction = q ≥ N * p
Thm      = q * (kₐ + kₜ) + p ≥ q * 4

-- The proof of Fraction follows by simple ≤-Reasoning using the ring solver.

fraction : Fraction
fraction = begin
  N * p
  ≤⟨ ≤-add-right (N * p) (N * 60 + 3) ⟩
  N * p + (N * 60 + 3)
  ≡⟨ step N ⟩
  q
  ∎
  where
  open ≤-Reasoning

  step : ∀ N → N * (N * 196 + 10) + (N * 60 + 3) ≡ N * N * 196 + N * 70 + 3
  step = Nat.solve-∀

-- For the proof of Thm we use the move sequence instantiated to m = n = N * 14.

m : ℕ
m = N * 14

n : ℕ
n = N * 14

mv : Moves
mv = seq m n ε

open MoveCounts (count mv) using (c#; t#; r#)
open RMoves kₐ kₜ

-- The move sequence mv is executable, since very sequence ought to.
hmv : ∃ λ leftover → rmoves mv rempty ≡ just (leftover ⨮ ε)
hmv = hyp mv ε (thm-seq m n)

-- Show lem from (thm-counts m n ε (proj₂ hm))
lem : c# * kₐ + t# * kₜ ≥ r#
lem with hmv
... | leftover , run =
  begin
    r#
  ≤⟨ ≤-add-right r# leftover ⟩
    r# + leftover
  ≤⟨ thm-counts mv 0 ε run ⟩
    c# * kₐ + (t# * kₜ + 0)
  ≡⟨ cong (c# * kₐ +_) (+-identityʳ (t# * kₜ)) ⟩
    c# * kₐ + t# * kₜ
  ∎

lem' : (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₜ
       ≥ N * 14 * (4 * (N * 14) + 3) + 3 * (N * 14) + 2
lem' =
  begin
    N * 14 * (4 * (N * 14) + 3) + 3 * (N * 14) + 2
  ≡⟨ sym (cong MoveCounts.r# (thm-counts-seq m n)) ⟩
    r#
  ≤⟨ lem ⟩
    c# * kₐ + t# * kₜ
  ≡⟨ cong (λ x → x * kₐ + t# * kₜ) (cong MoveCounts.c# (thm-counts-seq m n)) ⟩
    (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + t# * kₜ
  ≡⟨ cong (λ x → (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + x * kₜ)
           (cong MoveCounts.t# (thm-counts-seq m n)) ⟩
    (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₜ
  ∎

-- Use lem to show the thm.
thm : Thm
thm =
  begin
    q * 4
  ≡⟨ step₁ N ⟩
    p + (N * 14 * (4 * (N * 14) + 3) + 3 * (N * 14) + 2)
  ≤⟨ +-monoʳ-≤ p lem' ⟩
    p + ((N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₜ)
  ≤⟨ ≤-add-right
       (p + ((N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₜ))
       (N * 28 * (kₐ + kₜ)) ⟩
    (p + ((N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₜ))
      + N * 28 * (kₐ + kₜ)
  ≡⟨ step₂ N kₐ kₜ ⟩
    q * (kₐ + kₜ) + p
  ∎
  where
  open ≤-Reasoning

  step₁ : ∀ N → (N * N * 196 + N * 70 + 3) * 4 ≡ (N * 196 + 10) + (N * 14 * (4 * (N * 14) + 3) + 3 * (N * 14) + 2)
  step₁ = Nat.solve-∀

  step₂
    : ∀ N kₐ kₜ
    → ((N * 196 + 10) + ((N * 14 * (N * 14 + 2) + N * 14 + 3) * kₐ + (N * 14 * (N * 14 + 2) + N * 14 + 3) * kₜ))
      + N * 28 * (kₐ + kₜ)
      ≡ (N * N * 196 + N * 70 + 3) * (kₐ + kₜ) + (N * 196 + 10)
  step₂ = Nat.solve-∀
