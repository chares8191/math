module Artin-1-4 where

open import MatrixMul
open import Agda.Builtin.FromNat
open import Data.Vec using ([]; _∷_)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

A : Matrix 2 2
A = (ℤ.pos 1 ∷ ℤ.pos 2 ∷ []) ∷
    (ℤ.pos 0 ∷ ℤ.pos 1 ∷ []) ∷
    []

B : Matrix 2 3
B = (ℤ.pos 0 ∷ ℤ.pos 1 ∷ ℤ.pos 2 ∷ []) ∷
    (ℤ.pos 1 ∷ ℤ.pos 1 ∷ ℤ.pos 3 ∷ []) ∷
    []

C : Matrix 3 1
C = (ℤ.pos 1 ∷ []) ∷
    (ℤ.pos 4 ∷ []) ∷
    (ℤ.pos 3 ∷ []) ∷
    []



