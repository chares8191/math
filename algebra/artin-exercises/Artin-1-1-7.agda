module Artin-1-1-7 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_; map; zipWith; foldr′; lookup; tabulate)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

-- Setup 3x3 Matrix Definitions
Matrix : Set
Matrix = Vec (Vec ℕ 3) 3

Ind₁ : Fin 3
Ind₁ = fzero

Ind₂ : Fin 3
Ind₂ = fsuc fzero

Ind₃ : Fin 3
Ind₃ = fsuc (fsuc fzero)

Elem : Fin 3 → Fin 3 → Matrix → ℕ
Elem i j mat = lookup (lookup mat i) j

Row : Fin 3 → Matrix → Vec ℕ 3
Row i mat = lookup mat i

Col : Fin 3 → Matrix → Vec ℕ 3
Col j mat = map (λ row → lookup row j) mat

dot : Vec ℕ 3 → Vec ℕ 3 → ℕ
dot xs ys = foldr′ _+_ 0 (zipWith _*_ xs ys)

matMul : Matrix → Matrix → Matrix
matMul A B = map (λ row → tabulate (λ j → dot row (Col j B))) A

-- Setup Matrix A
Row₁A : Vec ℕ 3
Row₁A = 1 ∷ 1 ∷ 1 ∷ []

Row₂A : Vec ℕ 3
Row₂A = 0 ∷ 1 ∷ 1 ∷ []

Row₃A : Vec ℕ 3
Row₃A = 0 ∷ 0 ∷ 1 ∷ []

A¹ : Matrix
A¹ = Row₁A ∷ Row₂A ∷ Row₃A ∷ []




Col₁ : Matrix → Vec ℕ 3
Col₁ B = Col Ind₁ B

Col₂ : Matrix → Vec ℕ 3
Col₂ B = Col Ind₂ B

Col₃ : Matrix → Vec ℕ 3
Col₃ B = Col Ind₃ B

-- Setup ProductA
ProductA : Matrix → Matrix
ProductA B = matMul A¹ B

ProductA-Row₁ : Matrix → Vec ℕ 3
ProductA-Row₁ B =
  dot Row₁A (Col Ind₁ B) ∷
  dot Row₁A (Col Ind₂ B) ∷
  dot Row₁A (Col Ind₃ B) ∷ []

ProductA-Row₂ : Matrix → Vec ℕ 3
ProductA-Row₂ B =
  dot Row₂A (Col₁ B) ∷
  dot Row₂A (Col₂ B) ∷
  dot Row₂A (Col₃ B) ∷ []

ProductA-Row₃ : Matrix → Vec ℕ 3
ProductA-Row₃ B =
  dot Row₃A (Col₁ B) ∷
  dot Row₃A (Col₂ B) ∷
  dot Row₃A (Col₃ B) ∷ []

ProductAB≡expected : ∀ B → ProductA B ≡
  ProductA-Row₁ B ∷
  ProductA-Row₂ B ∷
  ProductA-Row₃ B ∷ []
ProductAB≡expected B = refl

-- Setup Matrix I
Vec₁I : Vec ℕ 3
Vec₁I = 1 ∷ 0 ∷ 0 ∷ []

Vec₂I : Vec ℕ 3
Vec₂I = 0 ∷ 1 ∷ 0 ∷ []

Vec₃I : Vec ℕ 3
Vec₃I = 0 ∷ 0 ∷ 1 ∷ []

I : Matrix
I = Vec₁I ∷ Vec₂I ∷ Vec₃I ∷ []

ProductAI≡expected : ProductA I ≡ A¹
ProductAI≡expected = refl

-- Setup PowerA
PowerA : ℕ → Matrix
PowerA zero = I
PowerA (suc n) = ProductA (PowerA n)

-- Line 
-- I : Matrix 3 3
-- I =
--   ( 1 ∷  0 ∷  0 ∷ []) ∷
--   ( 0 ∷  1 ∷  0 ∷ []) ∷
--   ( 0 ∷  0 ∷  1 ∷ []) ∷ []
-- 
-- Tr : ℕ → ℕ
-- Tr zero = 0
-- Tr (suc n) = Tr n + suc n
-- 
-- ClosedFormAⁿ : ℕ → Matrix 3 3
-- ClosedFormAⁿ n =
--   ( 1 ∷  n ∷  (Tr n) ∷ []) ∷
--   ( 0 ∷  1 ∷  n      ∷ []) ∷
--   ( 0 ∷  0 ∷  1      ∷ []) ∷ []
-- 
-- A² : Matrix 3 3
-- A² =
--   ( 1 ∷  2 ∷  3 ∷ []) ∷
--   ( 0 ∷  1 ∷  2 ∷ []) ∷
--   ( 0 ∷  0 ∷  1 ∷ []) ∷ []
-- 
-- ProductA²≡expected : ProductA A ≡ A²
-- ProductA²≡expected = refl
-- 
-- PowerA : ℕ → Matrix 3 3
-- PowerA zero = I
-- PowerA (suc n) = ProductA (PowerA n)
-- 
-- -- Goal: ClosedFormAⁿ is correct
-- 
-- closed-form-base :
--   ClosedFormAⁿ zero ≡ I
-- closed-form-base = refl
-- 
-- closed-form-step :
--   ∀ n → ProductA (ClosedFormAⁿ n) ≡ ClosedFormAⁿ (suc n)
-- closed-form-step n =
--   begin
--     ProductA (ClosedFormAⁿ n)
--   ≡⟨⟩
--     matMul (ClosedFormAⁿ n) A
--   ≡⟨⟩
--     ( 1 ∷  (suc n) ∷  (Tr n + suc n) ∷ []) ∷
--     ( 0 ∷  1       ∷  (suc n)        ∷ []) ∷
--     ( 0 ∷  0       ∷  1              ∷ []) ∷ []
--   ≡⟨⟩
--     ClosedFormAⁿ (suc n)
--   ∎


