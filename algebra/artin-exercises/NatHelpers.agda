module NatHelpers where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

-- ℕ Arithmetic Lemmas
*-zeroʳ : ∀ n → n * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl

*-zeroˡ : ∀ n → n * zero ≡ zero
*-zeroˡ zero = refl
*-zeroˡ (suc n) rewrite *-zeroˡ n = refl

*-oneʳ : ∀ n → n * suc zero ≡ n
*-oneʳ zero = refl
*-oneʳ (suc n) rewrite *-oneʳ n = refl

*-oneˡ : ∀ n → n * suc zero ≡ n
*-oneˡ zero = refl
*-oneˡ (suc n) rewrite *-oneˡ n = refl

+-zeroˡ : ∀ n → zero + n ≡ n
+-zeroˡ zero = refl
+-zeroˡ (suc n) rewrite +-zeroˡ n = refl

+-zeroʳ : ∀ n → n + zero ≡ n
+-zeroʳ zero = refl
+-zeroʳ (suc n) rewrite +-zeroʳ n = refl

+-oneʳ : ∀ n → n + (suc zero) ≡ suc n
+-oneʳ zero = refl
+-oneʳ (suc n) rewrite +-oneʳ n = refl

+-oneˡ : ∀ n → (suc zero) + n ≡ suc n
+-oneˡ zero = refl
+-oneˡ (suc n) rewrite +-oneˡ n = refl

suc-sumʳ : ∀ x y → x + (suc y) ≡ (suc (x + y))
suc-sumʳ zero y = refl
suc-sumʳ (suc x) y rewrite suc-sumʳ x y = refl

suc-sumˡ : ∀ x y → suc(x) + y ≡ (suc (x + y))
suc-sumˡ x y = refl

NatSum-Commutative : ∀ x y → (x + y) ≡ (y + x)
NatSum-Commutative zero y rewrite +-zeroʳ y = refl
NatSum-Commutative (suc x) y
  rewrite NatSum-Commutative x y
        | suc-sumʳ y x
  = refl

-- NatMult-Commutative : ∀ x y → (x * y) ≡ (y * x)
-- NatMult-Commutative zero y rewrite *-zeroʳ y = refl

