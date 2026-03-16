module Artin-1-1-8 where

open import MatrixMul
open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using ([]; _∷_)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

-- Worked out on paper with block multiplication.

M₁ : Matrix 4 4
M₁ =
  (1 ∷ 1 ∷ 1 ∷ 5 ∷ []) ∷
  (0 ∷ 1 ∷ 0 ∷ 1 ∷ []) ∷
  (1 ∷ 0 ∷ 0 ∷ 1 ∷ []) ∷
  (0 ∷ 1 ∷ 1 ∷ 0 ∷ []) ∷ []

M₁′ : Matrix 4 4
M₁′ =
  (1 ∷ 2 ∷ 1 ∷ 0 ∷ []) ∷
  (0 ∷ 1 ∷ 0 ∷ 1 ∷ []) ∷
  (1 ∷ 0 ∷ 0 ∷ 1 ∷ []) ∷
  (0 ∷ 1 ∷ 1 ∷ 3 ∷ []) ∷ []

Expected₁ : Matrix 4 4
Expected₁ =
  (2 ∷ 8 ∷ 6 ∷ 17 ∷ []) ∷
  (0 ∷ 2 ∷ 1 ∷ 4  ∷ []) ∷
  (1 ∷ 3 ∷ 2 ∷ 3  ∷ []) ∷
  (1 ∷ 1 ∷ 0 ∷ 2  ∷ []) ∷ []

Product₁≡expected : matMul M₁ M₁′ ≡ Expected₁
Product₁≡expected = refl

M₂ : Matrix 3 3
M₂ =
  (0 ∷ 1 ∷ 2 ∷ []) ∷
  (0 ∷ 1 ∷ 0 ∷ []) ∷
  (3 ∷ 0 ∷ 1 ∷ []) ∷ []

M₂′ : Matrix 3 3
M₂′ =
  (1 ∷ 2 ∷ 3 ∷ []) ∷
  (4 ∷ 2 ∷ 3 ∷ []) ∷
  (5 ∷ 0 ∷ 4 ∷ []) ∷ []

Expected₂ : Matrix 3 3
Expected₂ =
  (14 ∷ 2 ∷ 11 ∷ []) ∷
  (4  ∷ 2 ∷ 3  ∷ []) ∷
  (8  ∷ 6 ∷ 13 ∷ []) ∷ []

Product₂≡expected : matMul M₂ M₂′ ≡ Expected₂
Product₂≡expected = refl

