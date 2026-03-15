module Artin-1-1-7 where

open import MatrixMul
open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using ([]; _∷_)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)


ClosedFormA¹ : Matrix 3 3
ClosedFormA¹ =
  (ℤ.pos 1 ∷ ℤ.pos 1 ∷ ℤ.pos 1 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 1 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1 ∷ []) ∷ []

ClosedFormI : Matrix 3 3
ClosedFormI =
  (ℤ.pos 1 ∷ ℤ.pos 0 ∷ ℤ.pos 0 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 0 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1 ∷ []) ∷ []

Tr : ℕ → ℕ
Tr zero = 0
Tr (suc n) = Tr n + suc n

ClosedFormAⁿ : ℕ → Matrix 3 3
ClosedFormAⁿ n =
  (ℤ.pos 1 ∷ ℤ.pos n ∷ ℤ.pos (Tr n) ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos n      ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1      ∷ []) ∷ []

ProductA : (Acc : Matrix 3 3) → Matrix 3 3
ProductA Acc = matMul Acc ClosedFormA¹

ClosedFormA² : Matrix 3 3
ClosedFormA² =
  (ℤ.pos 1 ∷ ℤ.pos 2 ∷ ℤ.pos 3 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 2 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1 ∷ []) ∷ []

ProductA²≡expected : ProductA ClosedFormA¹ ≡ ClosedFormA²
ProductA²≡expected = refl

PowerA : ℕ → Matrix 3 3
PowerA zero = ClosedFormI
PowerA (suc n) = ProductA (PowerA n)

-- To Show: ClosedFormAⁿ is correct

closed-form-base :
  ClosedFormAⁿ zero ≡ ClosedFormI
closed-form-base = refl

-- closed-form-step : ∀ n → ProductA (ClosedFormAⁿ n) ≡ ClosedFormAⁿ (suc n)
-- closed-form-step n = {!!}
