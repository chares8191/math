module Artin-1-1-7 where

open import MatrixMul
open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using ([]; _∷_)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

A : Matrix 3 3
A =
  (ℤ.pos 1 ∷ ℤ.pos 1 ∷ ℤ.pos 1 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 1 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1 ∷ []) ∷ []

A² : Matrix 3 3
A² =
  (ℤ.pos 1 ∷ ℤ.pos 2 ∷ ℤ.pos 3 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 2 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1 ∷ []) ∷ []

A²-correct : A² ≡ matPow 2 A
A²-correct = refl

A³ : Matrix 3 3
A³ =
  (ℤ.pos 1 ∷ ℤ.pos 3 ∷ ℤ.pos 6 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 3 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1 ∷ []) ∷ []

A³-correct : A³ ≡ matPow 3 A
A³-correct = refl

A⁴ : Matrix 3 3
A⁴ =
  (ℤ.pos 1 ∷ ℤ.pos 4 ∷ ℤ.pos 10 ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 4  ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1  ∷ []) ∷ []

A⁴-correct : A⁴ ≡ matPow 4 A
A⁴-correct = refl

Triangular : ℕ → ℕ
Triangular zero = 0
Triangular (suc n) = Triangular n + (n + 1)

Aⁿ : ℕ → Matrix 3 3
Aⁿ n =
  (ℤ.pos 1 ∷ ℤ.pos n ∷ ℤ.pos (Triangular n) ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos n              ∷ []) ∷
  (ℤ.pos 0 ∷ ℤ.pos 0 ∷ ℤ.pos 1              ∷ []) ∷ []
