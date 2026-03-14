module Artin-1-5 where

open import MatrixMul
open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≤?_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

matMulLeft : ∀ {l m n p} → Matrix l m → Matrix m n → Matrix n p → Matrix l p
matMulLeft A B C = matMul (matMul A B) C

matMulRight : ∀ {l m n p} → Matrix l m → Matrix m n → Matrix n p → Matrix l p
matMulRight A B C = matMul A (matMul B C)

Cost : ∀ {l m n} → Matrix l m → Matrix m n → ℕ
Cost {l} {m} {n} _ _ = l * m * n

matMulLeftCost : ∀ {l m n p} → Matrix l m → Matrix m n → Matrix n p → ℕ
matMulLeftCost A B C = Cost A B + Cost (matMul A B) C

matMulRightCost : ∀ {l m n p} → Matrix l m → Matrix m n → Matrix n p → ℕ
matMulRightCost A B C = Cost B C + Cost A (matMul B C)

LeftCost : ℕ → ℕ → ℕ → ℕ → ℕ
LeftCost l m n p = l * m * n + l * n * p

RightCost : ℕ → ℕ → ℕ → ℕ → ℕ
RightCost l m n p =  m * n * p + l * m * p

matMulLeftCost-actual :
  ∀ {l m n p} (A : Matrix l m) (B : Matrix m n) (C : Matrix n p) →
  matMulLeftCost A B C ≡ LeftCost l m n p
matMulLeftCost-actual A B C = refl

matMulRightCost-actual :
  ∀ {l m n p} (A : Matrix l m) (B : Matrix m n) (C : Matrix n p) →
  matMulRightCost A B C ≡ RightCost l m n p
matMulRightCost-actual A B C = refl


