module Artin-1-1-7 where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_; map; zipWith; foldr′; lookup; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

-- Matrix Setup

Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vec ℕ n) m

dot : ∀ {n} → Vec ℕ n → Vec ℕ n → ℕ
dot xs ys = foldr′ _+_ 0 (zipWith _*_ xs ys)

col : ∀ {m n} → Fin n → Matrix m n → Vec ℕ m
col j mat = map (λ row → lookup row j) mat

matMul : ∀ {m n p} → Matrix m n → Matrix n p → Matrix m p
matMul A B = map (λ row → tabulate (λ j → dot row (col j B))) A

-- Goal Setup

ClosedFormA¹ : Matrix 3 3
ClosedFormA¹ =
  ( 1 ∷  1 ∷  1 ∷ []) ∷
  ( 0 ∷  1 ∷  1 ∷ []) ∷
  ( 0 ∷  0 ∷  1 ∷ []) ∷ []

ClosedFormI : Matrix 3 3
ClosedFormI =
  ( 1 ∷  0 ∷  0 ∷ []) ∷
  ( 0 ∷  1 ∷  0 ∷ []) ∷
  ( 0 ∷  0 ∷  1 ∷ []) ∷ []

Tr : ℕ → ℕ
Tr zero = 0
Tr (suc n) = Tr n + suc n

ClosedFormAⁿ : ℕ → Matrix 3 3
ClosedFormAⁿ n =
  ( 1 ∷  n ∷  (Tr n) ∷ []) ∷
  ( 0 ∷  1 ∷  n      ∷ []) ∷
  ( 0 ∷  0 ∷  1      ∷ []) ∷ []

ProductA : (Acc : Matrix 3 3) → Matrix 3 3
ProductA Acc = matMul Acc ClosedFormA¹

ClosedFormA² : Matrix 3 3
ClosedFormA² =
  ( 1 ∷  2 ∷  3 ∷ []) ∷
  ( 0 ∷  1 ∷  2 ∷ []) ∷
  ( 0 ∷  0 ∷  1 ∷ []) ∷ []

ProductA²≡expected : ProductA ClosedFormA¹ ≡ ClosedFormA²
ProductA²≡expected = refl

PowerA : ℕ → Matrix 3 3
PowerA zero = ClosedFormI
PowerA (suc n) = ProductA (PowerA n)

-- Goal: ClosedFormAⁿ is correct

closed-form-base :
  ClosedFormAⁿ zero ≡ ClosedFormI
closed-form-base = refl

closed-form-step : ∀ n → ProductA (ClosedFormAⁿ n) ≡ ClosedFormAⁿ (suc n)
closed-form-step n = {!!}
