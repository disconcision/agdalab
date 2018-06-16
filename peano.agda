module peano where

--import Relation.Binary.PropositionalEquality as Eq
--open Eq using (_≡_; refl)
--open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- in the beginning, there are no natural numbers

-- on the first day, there is one natural number   

{-
_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + n = n
(suc n) + n′ = suc(n + n′)

data _even : ℕ → Set where
  ZERO : zero even
  STEP : ∀ x → x even → suc (suc x) even

proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)
-- C-c C-space

-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc(m + n)
     
aa : ℕ
aa = suc (suc zero)

{-# BUILTIN NATURAL ℕ #-}

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩
    suc ((suc zero)+(suc(suc(suc zero))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 4 ≡ 6
_ = refl


_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ zero = suc zero
n ^ (suc m) = n * (n ^ m)


_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ (suc n) = zero
(suc m) ∸ (suc n) = m ∸ n 


