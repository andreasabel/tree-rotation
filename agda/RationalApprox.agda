{-# OPTIONS --safe #-}

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

open import Library hiding (m; n)
open import Tree using (ε)
open import SingleTreeGame using (Moves; ε; moves)
open import Sequence using (seq; thm-seq)
open import RationalSingleTreeGame
  using (rempty; module RMoves; [_]ℚ; [+]ℚ; _⨮_)
open import Counting using (MoveCounts; count; C:_T:_R:_; thm-counts-seq)

open import Data.Integer using (+≤+; +<+)
open import Data.Rational
open import Data.Rational.Properties using
  ( +-identityˡ; +-identityʳ; +-assoc; +-comm
  ; *-zeroˡ; *-identityʳ; *-comm; *-assoc; *-inverseˡ
  ; ≤-refl; ≤-reflexive; ≤-trans; <⇒≤; <-≤-trans; ≤-<-trans
  ; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; +-monoˡ-<
  ; *-monoʳ-≤-nonNeg
  ; *-cancelˡ-≤-pos; *-cancelˡ-<-nonNeg
  ; positive⁻¹; 1/pos⇒pos; pos⇒nonNeg; pos⇒nonZero
  ; module ≤-Reasoning)
import Data.Rational.Tactic.RingSolver as ℚ

open ℕ using (z≤n; s≤s)

module RationalApprox
  -- Budget for concat and tail.
  (kₐ kₜ : ℚ)
  -- The budgets are non-negative.
  (kₐ-pos : 0ℚ ≤ kₐ)
  (kₜ-pos : 0ℚ ≤ kₜ)
  -- We assume that this budget is sufficient to execute any legal move sequence,
  -- and that the leftover resource is non-negative.
  (hyp : ∀ mv t
   → moves mv ε ≡ just t
   → ∃ λ leftover → 0ℚ ≤ leftover × RMoves.rmoves kₐ kₜ mv rempty ≡ just (leftover ⨮ t))
  -- Approximation precision as N goes to +∞.
  (N : ℕ)
  where

p : ℕ
p = N ℕ.* 196 ℕ.+ 10

q : ℕ
q = N ℕ.* N ℕ.* 196 ℕ.+ N ℕ.* 70 ℕ.+ 3

-- We are showing these two theorems:

Fraction = q ℕ.≥ N ℕ.* p

Thm = [ q ]ℚ * (kₐ + kₜ) + [ p ]ℚ ≥ [ q ℕ.* 4 ]ℚ

-- The proof of Fraction follows by simple ≤-Reasoning over ℕ using the ring solver.

fraction : Fraction
fraction = let open ℕ.≤-Reasoning in
  begin
    N ℕ.* p
  ≤⟨ ℕ.m≤m+n (N ℕ.* p) (N ℕ.* 60 ℕ.+ 3) ⟩
    N ℕ.* p ℕ.+ (N ℕ.* 60 ℕ.+ 3)
  ≡⟨ step N ⟩
    q
  ∎
  where
  step : ∀ N → N ℕ.* (N ℕ.* 196 ℕ.+ 10) ℕ.+ (N ℕ.* 60 ℕ.+ 3) ≡ N ℕ.* N ℕ.* 196 ℕ.+ N ℕ.* 70 ℕ.+ 3
  step = ℕ.solve-∀

-- For the proof of Thm we use the move sequence instantiated to m = n = N * 14.

m : ℕ
m = N ℕ.* 14

n : ℕ
n = N ℕ.* 14

mv : Moves
mv = seq m n ε

open MoveCounts (count mv) using (c#; t#; r#)
open RMoves kₐ kₜ
open ≤-Reasoning

-- The move sequence mv is executable, since every sequence ought to.
hmv : ∃ λ leftover → 0ℚ ≤ leftover × rmoves mv rempty ≡ just (leftover ⨮ ε)
hmv = hyp mv ε (thm-seq m n)

-- Small helpers on ℚ inequalities.

≤-add-right : ∀ {a b : ℚ} → 0ℚ ≤ b → a ≤ a + b
≤-add-right {a} {b} 0≤b = ≤-trans (≤-reflexive (sym (+-identityʳ a))) (+-monoʳ-≤ a 0≤b)

+-pos : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
+-pos {a} {b} 0≤a 0≤b = ≤-trans (≤-reflexive (sym (+-identityˡ 0ℚ))) (+-mono-≤ 0≤a 0≤b)

*-pos : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
*-pos {a} {b} 0≤a 0≤b =
  ≤-trans (≤-reflexive (sym (*-zeroˡ b)))
          (*-monoʳ-≤-nonNeg b {{nonNegative 0≤b}} 0≤a)

0≤1ℚ : 0ℚ ≤ 1ℚ
0≤1ℚ = *≤* (+≤+ z≤n)

[]-pos : ∀ k → 0ℚ ≤ [ k ]ℚ
[]-pos zero    = ≤-refl
[]-pos (suc k) = +-pos 0≤1ℚ ([]-pos k)

kₐ+kₜ-pos : 0ℚ ≤ kₐ + kₜ
kₐ+kₜ-pos = +-pos kₐ-pos kₜ-pos

-- lem : From the resourced run, derive that the R-count is bounded by C·kₐ + T·kₜ.
lem : [ c# ]ℚ * kₐ + [ t# ]ℚ * kₜ ≥ [ r# ]ℚ
lem with hmv
... | leftover , 0≤lo , run =
  begin
    [ r# ]ℚ
  ≤⟨ ≤-add-right 0≤lo ⟩
    [ r# ]ℚ + leftover
  ≤⟨ thm-counts mv 0ℚ ε run ⟩
    [ c# ]ℚ * kₐ + ([ t# ]ℚ * kₜ + 0ℚ)
  ≡⟨ cong ([ c# ]ℚ * kₐ +_) (+-identityʳ ([ t# ]ℚ * kₜ)) ⟩
    [ c# ]ℚ * kₐ + [ t# ]ℚ * kₜ
  ∎

-- lem' : Same as lem but with c#, t#, r# spelled out via the closed form from thm-counts-seq.
lem' : [ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₐ
     + [ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₜ
     ≥ [ N ℕ.* 14 ℕ.* (4 ℕ.* (N ℕ.* 14) ℕ.+ 3) ℕ.+ 3 ℕ.* (N ℕ.* 14) ℕ.+ 2 ]ℚ
lem' =
  begin
    [ N ℕ.* 14 ℕ.* (4 ℕ.* (N ℕ.* 14) ℕ.+ 3) ℕ.+ 3 ℕ.* (N ℕ.* 14) ℕ.+ 2 ]ℚ
  ≡⟨ sym (cong (λ x → [ MoveCounts.r# x ]ℚ) (thm-counts-seq m n)) ⟩
    [ r# ]ℚ
  ≤⟨ lem ⟩
    [ c# ]ℚ * kₐ + [ t# ]ℚ * kₜ
  ≡⟨ cong (λ x → [ MoveCounts.c# x ]ℚ * kₐ + [ MoveCounts.t# x ]ℚ * kₜ) (thm-counts-seq m n) ⟩
    [ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₐ
    + [ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₜ
  ∎

-- Use lem' to show Thm.
thm : Thm
thm =
  begin
    [ q ℕ.* 4 ]ℚ
  ≡⟨ cong [_]ℚ (step₁ N) ⟩
    [ p ℕ.+ (N ℕ.* 14 ℕ.* (4 ℕ.* (N ℕ.* 14) ℕ.+ 3) ℕ.+ 3 ℕ.* (N ℕ.* 14) ℕ.+ 2) ]ℚ
  ≡⟨ [+]ℚ p (N ℕ.* 14 ℕ.* (4 ℕ.* (N ℕ.* 14) ℕ.+ 3) ℕ.+ 3 ℕ.* (N ℕ.* 14) ℕ.+ 2) ⟩
    [ p ]ℚ + [ N ℕ.* 14 ℕ.* (4 ℕ.* (N ℕ.* 14) ℕ.+ 3) ℕ.+ 3 ℕ.* (N ℕ.* 14) ℕ.+ 2 ]ℚ
  ≤⟨ +-monoʳ-≤ [ p ]ℚ lem' ⟩
    [ p ]ℚ + ([ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₐ
              + [ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₜ)
  ≤⟨ ≤-add-right (*-pos ([]-pos (N ℕ.* 28)) kₐ+kₜ-pos) ⟩
    ([ p ]ℚ + ([ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₐ
               + [ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ * kₜ))
      + [ N ℕ.* 28 ]ℚ * (kₐ + kₜ)
  ≡⟨ step₂' [ p ]ℚ [ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ [ N ℕ.* 28 ]ℚ ⟩
    ([ N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3 ]ℚ + [ N ℕ.* 28 ]ℚ) * (kₐ + kₜ) + [ p ]ℚ
  ≡⟨ cong (λ x → x * (kₐ + kₜ) + [ p ]ℚ)
       (sym ([+]ℚ (N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3) (N ℕ.* 28))) ⟩
    [ (N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3) ℕ.+ N ℕ.* 28 ]ℚ * (kₐ + kₜ) + [ p ]ℚ
  ≡⟨ cong (λ x → [ x ]ℚ * (kₐ + kₜ) + [ p ]ℚ) (sym (q-as-c+d N)) ⟩
    [ q ]ℚ * (kₐ + kₜ) + [ p ]ℚ
  ∎
  where
  step₁ : ∀ N → (N ℕ.* N ℕ.* 196 ℕ.+ N ℕ.* 70 ℕ.+ 3) ℕ.* 4
              ≡ (N ℕ.* 196 ℕ.+ 10)
                ℕ.+ (N ℕ.* 14 ℕ.* (4 ℕ.* (N ℕ.* 14) ℕ.+ 3) ℕ.+ 3 ℕ.* (N ℕ.* 14) ℕ.+ 2)
  step₁ = ℕ.solve-∀

  q-as-c+d : ∀ N → N ℕ.* N ℕ.* 196 ℕ.+ N ℕ.* 70 ℕ.+ 3
                 ≡ (N ℕ.* 14 ℕ.* (N ℕ.* 14 ℕ.+ 2) ℕ.+ N ℕ.* 14 ℕ.+ 3) ℕ.+ N ℕ.* 28
  q-as-c+d = ℕ.solve-∀

  step₂' : ∀ (P C D : ℚ)
         → (P + (C * kₐ + C * kₜ)) + D * (kₐ + kₜ) ≡ (C + D) * (kₐ + kₜ) + P
  step₂' P C D = step kₐ kₜ P C D
    where
    step : ∀ (kₐ kₜ P C D : ℚ)
         → (P + (C * kₐ + C * kₜ)) + D * (kₐ + kₜ) ≡ (C + D) * (kₐ + kₜ) + P
    step = ℚ.solve-∀

-- A consequence: there is 0 ≤ r < 1/N such that kₐ + kₜ ≥ 4 - r.
-- We pick r = p/q.

-- Multiplicative homomorphism for the ℕ → ℚ embedding.
[*]ℚ : ∀ a b → [ a ℕ.* b ]ℚ ≡ [ a ]ℚ * [ b ]ℚ
[*]ℚ zero    b = sym (*-zeroˡ [ b ]ℚ)
[*]ℚ (suc a) b
  = trans ([+]ℚ b (a ℕ.* b))
          (trans (cong ([ b ]ℚ +_) ([*]ℚ a b))
                 (sym (step [ a ]ℚ [ b ]ℚ)))
  where
  step : ∀ x y → (1ℚ + x) * y ≡ y + x * y
  step = ℚ.solve-∀

-- Order-preservation of the ℕ → ℚ embedding.
[≤]ℚ : ∀ {a b} → a ℕ.≤ b → [ a ]ℚ ≤ [ b ]ℚ
[≤]ℚ {zero}  {b}     z≤n     = []-pos b
[≤]ℚ {suc a} {suc b} (s≤s p) = +-monoʳ-≤ 1ℚ ([≤]ℚ p)

0<1ℚ : 0ℚ < 1ℚ
0<1ℚ = *<* (+<+ (s≤s z≤n))

[<]ℚ : ∀ {a b} → a ℕ.< b → [ a ]ℚ < [ b ]ℚ
[<]ℚ {a} {b} sa≤b =
  begin-strict
    [ a ]ℚ
  ≡⟨ sym (+-identityˡ [ a ]ℚ) ⟩
    0ℚ + [ a ]ℚ
  <⟨ +-monoˡ-< [ a ]ℚ 0<1ℚ ⟩
    1ℚ + [ a ]ℚ
  ≤⟨ [≤]ℚ sa≤b ⟩
    [ b ]ℚ
  ∎

-- q is positive.
q-as-suc : q ≡ suc (N ℕ.* N ℕ.* 196 ℕ.+ N ℕ.* 70 ℕ.+ 2)
q-as-suc = ℕ.+-suc (N ℕ.* N ℕ.* 196 ℕ.+ N ℕ.* 70) 2

0<q-ℕ : 0 ℕ.< q
0<q-ℕ = subst (0 ℕ.<_) (sym q-as-suc) (s≤s z≤n)

[q]-positive : 0ℚ < [ q ]ℚ
[q]-positive = [<]ℚ 0<q-ℕ

instance
  Pos-[q] : Positive [ q ]ℚ
  Pos-[q] = positive [q]-positive

  NZ-[q] : NonZero [ q ]ℚ
  NZ-[q] = pos⇒nonZero [ q ]ℚ

-- Strict version of fraction.
Np<q : N ℕ.* p ℕ.< q
Np<q = subst (N ℕ.* p ℕ.<_) q-form (ℕ.m<m+n (N ℕ.* p) 0<60N+3)
  where
  q-form : N ℕ.* p ℕ.+ (N ℕ.* 60 ℕ.+ 3) ≡ q
  q-form = step N
    where
    step : ∀ N → N ℕ.* (N ℕ.* 196 ℕ.+ 10) ℕ.+ (N ℕ.* 60 ℕ.+ 3) ≡ N ℕ.* N ℕ.* 196 ℕ.+ N ℕ.* 70 ℕ.+ 3
    step = ℕ.solve-∀

  0<60N+3 : 0 ℕ.< N ℕ.* 60 ℕ.+ 3
  0<60N+3 = subst (0 ℕ.<_) (sym (ℕ.+-suc (N ℕ.* 60) 2)) (s≤s z≤n)

-- The rational witness r = p/q.
r : ℚ
r = [ p ]ℚ ÷ [ q ]ℚ

-- The defining property: r · q = p.
r*q≡p : r * [ q ]ℚ ≡ [ p ]ℚ
r*q≡p
  = trans (*-assoc [ p ]ℚ (1/ [ q ]ℚ) [ q ]ℚ)
  ( trans (cong ([ p ]ℚ *_) (*-inverseˡ [ q ]ℚ))
          (*-identityʳ [ p ]ℚ))

0≤r : 0ℚ ≤ r
0≤r = *-pos ([]-pos p) (<⇒≤ (positive⁻¹ (1/ [ q ]ℚ) {{1/pos⇒pos [ q ]ℚ}}))

-- r * N < 1, i.e., r < 1/N.
r*N<1 : r * [ N ]ℚ < 1ℚ
r*N<1 = *-cancelˡ-<-nonNeg [ q ]ℚ {{pos⇒nonNeg [ q ]ℚ}}
  (begin-strict
    [ q ]ℚ * (r * [ N ]ℚ)
  ≡⟨ rearrange [ q ]ℚ r [ N ]ℚ ⟩
    (r * [ q ]ℚ) * [ N ]ℚ
  ≡⟨ cong (_* [ N ]ℚ) r*q≡p ⟩
    [ p ]ℚ * [ N ]ℚ
  ≡⟨ sym ([*]ℚ p N) ⟩
    [ p ℕ.* N ]ℚ
  ≡⟨ cong [_]ℚ (ℕ.*-comm p N) ⟩
    [ N ℕ.* p ]ℚ
  <⟨ [<]ℚ Np<q ⟩
    [ q ]ℚ
  ≡⟨ sym (*-identityʳ [ q ]ℚ) ⟩
    [ q ]ℚ * 1ℚ
  ∎)
  where
  rearrange : ∀ a b c → a * (b * c) ≡ (b * a) * c
  rearrange = ℚ.solve-∀

-- kₐ + kₜ + r ≥ 4.
sum+r≥4 : kₐ + kₜ + r ≥ [ 4 ]ℚ
sum+r≥4 = *-cancelˡ-≤-pos [ q ]ℚ
  (begin
    [ q ]ℚ * [ 4 ]ℚ
  ≡⟨ sym ([*]ℚ q 4) ⟩
    [ q ℕ.* 4 ]ℚ
  ≤⟨ thm ⟩
    [ q ]ℚ * (kₐ + kₜ) + [ p ]ℚ
  ≡⟨ cong ([ q ]ℚ * (kₐ + kₜ) +_) (sym r*q≡p) ⟩
    [ q ]ℚ * (kₐ + kₜ) + r * [ q ]ℚ
  ≡⟨ rearrange [ q ]ℚ (kₐ + kₜ) r ⟩
    [ q ]ℚ * (kₐ + kₜ + r)
  ∎)
  where
  rearrange : ∀ q s r → q * s + r * q ≡ q * (s + r)
  rearrange = ℚ.solve-∀

-- kₐ + kₜ ≥ 4 - r.
sum≥4-r : kₐ + kₜ ≥ [ 4 ]ℚ - r
sum≥4-r =
  begin
    [ 4 ]ℚ - r
  ≤⟨ +-monoˡ-≤ (- r) sum+r≥4 ⟩
    (kₐ + kₜ + r) + (- r)
  ≡⟨ rearrange kₐ kₜ r ⟩
    kₐ + kₜ
  ∎
  where
  rearrange : ∀ a b r → (a + b + r) + (- r) ≡ a + b
  rearrange = ℚ.solve-∀

-- The headline approximation statement, in the form requested.
Theorem = ∃ λ (r : ℚ)
  → 0ℚ ≤ r
  × r * [ N ]ℚ < 1ℚ
  × kₐ + kₜ ≥ [ 4 ]ℚ - r

theorem : Theorem
theorem = r , 0≤r , r*N<1 , sum≥4-r
