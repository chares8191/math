module Artin-1-1-7 where

open import NatHelpers
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_; map; zipWith; foldr′; lookup; tabulate)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

-- The baby steps kind of thing.

-- Index Literals
Idx₁ : Fin 3
Idx₁ = fzero

Idx₂ : Fin 3
Idx₂ = fsuc fzero

Idx₃ : Fin 3
Idx₃ = fsuc (fsuc fzero)

-- Triple Type
Triple : Set
Triple = Vec ℕ 3

-- Triple Element
VecElem : Triple → Fin 3 → ℕ
VecElem T k = lookup T k

Triple-Elem≡expected :
  ∀ T → VecElem T Idx₁ ∷ VecElem T Idx₂ ∷ VecElem T Idx₃ ∷ [] ≡ T
Triple-Elem≡expected (x ∷ y ∷ z ∷ []) = refl

-- Triple Product
VecProduct : Triple → Triple → ℕ
VecProduct X Y =
  (VecElem X Idx₁ * VecElem Y Idx₁) +
  (VecElem X Idx₂ * VecElem Y Idx₂) +
  (VecElem X Idx₃ * VecElem Y Idx₃)

-- 3x3 Matrix Type
Matrix : Set
Matrix = Vec Triple 3

-- 3x3 Matrix Element
MtxElem : Matrix → Fin 3 → Fin 3 → ℕ
MtxElem M i j = VecElem (lookup M i) j

-- 3x3 Matrix Row
MtxRow : Matrix → Fin 3 → Triple
MtxRow M i =
  MtxElem M i Idx₁ ∷
  MtxElem M i Idx₂ ∷
  MtxElem M i Idx₃ ∷ []

MtxRow-Elem≡expected :
  ∀ M i j → VecElem (MtxRow M i) j ≡ MtxElem M i j
MtxRow-Elem≡expected M i fzero               = refl
MtxRow-Elem≡expected M i (fsuc fzero)        = refl
MtxRow-Elem≡expected M i (fsuc (fsuc fzero)) = refl

-- 3x3 Matrix Column
MtxCol : Matrix → Fin 3 → Triple
MtxCol M j =
  MtxElem M Idx₁ j ∷
  MtxElem M Idx₂ j ∷
  MtxElem M Idx₃ j ∷ []

MtxCol-Elem≡expected :
  ∀ M i j → VecElem (MtxCol M j) i ≡ MtxElem M i j
MtxCol-Elem≡expected M fzero j               = refl
MtxCol-Elem≡expected M (fsuc fzero) j        = refl
MtxCol-Elem≡expected M (fsuc (fsuc fzero)) j = refl

-- 3x3 Matrix Product Element
MtxProduct-Elem :
  Matrix →
  Matrix →
  Fin 3 →
  Fin 3 → ℕ
MtxProduct-Elem A B i j = VecProduct (MtxRow A i) (MtxCol B j)

MtxProduct-Elem-expected :
  Matrix →
  Matrix →
  Fin 3 →
  Fin 3 → ℕ
MtxProduct-Elem-expected A B i j =
  (MtxElem A i Idx₁) * (MtxElem B Idx₁ j) +
  (MtxElem A i Idx₂) * (MtxElem B Idx₂ j) +
  (MtxElem A i Idx₃) * (MtxElem B Idx₃ j)

MtxProduct-Elem≡expected :
  ∀ A B i j →
  MtxProduct-Elem A B i j ≡ MtxProduct-Elem-expected A B i j
MtxProduct-Elem≡expected A B i j = refl

-- 3x3 Matrix Product Row
MtxProduct-Row : Matrix → Matrix → Fin 3 → Triple
MtxProduct-Row A B i =
  VecProduct (MtxRow A i) (MtxCol B Idx₁) ∷
  VecProduct (MtxRow A i) (MtxCol B Idx₂) ∷
  VecProduct (MtxRow A i) (MtxCol B Idx₃) ∷ []

MtxProduct-Row-expected : Matrix → Matrix → Fin 3 → Triple
MtxProduct-Row-expected A B i =
  MtxProduct-Elem-expected A B i Idx₁ ∷
  MtxProduct-Elem-expected A B i Idx₂ ∷
  MtxProduct-Elem-expected A B i Idx₃ ∷ []

MtxProduct-Row≡expected :
  ∀ A B i →
  MtxProduct-Row A B i ≡ MtxProduct-Row-expected A B i
MtxProduct-Row≡expected A B i = refl

-- 3x3 Matrix Product
MtxProduct : Matrix → Matrix → Matrix
MtxProduct A B =
  MtxProduct-Row A B Idx₁ ∷
  MtxProduct-Row A B Idx₂ ∷
  MtxProduct-Row A B Idx₃ ∷ []

MtxProduct-expected : Matrix → Matrix → Matrix
MtxProduct-expected A B =
  MtxProduct-Row-expected A B Idx₁ ∷
  MtxProduct-Row-expected A B Idx₂ ∷
  MtxProduct-Row-expected A B Idx₃ ∷ []

MtxProduct≡expected :
  ∀ A B →
  MtxProduct A B ≡ MtxProduct-expected A B
MtxProduct≡expected A B = refl

-- Identity Basis Triple
VecIdy : Fin 3 → Triple
VecIdy fzero               = 1 ∷ 0 ∷ 0 ∷ []
VecIdy (fsuc fzero)        = 0 ∷ 1 ∷ 0 ∷ []
VecIdy (fsuc (fsuc fzero)) = 0 ∷ 0 ∷ 1 ∷ []

VecProduct-RightIdy≡expected :
  ∀ X k → VecProduct X (VecIdy k) ≡ VecElem X k
VecProduct-RightIdy≡expected X fzero
  rewrite *-oneʳ  (VecElem X Idx₁)
        | *-zeroʳ (VecElem X Idx₂)
        | *-zeroʳ (VecElem X Idx₃)
        | +-zeroʳ (VecElem X Idx₁)
        | +-zeroʳ (VecElem X Idx₁)
  = refl
VecProduct-RightIdy≡expected X (fsuc fzero)
  rewrite *-zeroʳ (VecElem X Idx₁)
        | *-oneʳ  (VecElem X Idx₂)
        | *-zeroʳ (VecElem X Idx₃)
        | +-zeroʳ (VecElem X Idx₂)
  = refl
VecProduct-RightIdy≡expected X (fsuc (fsuc fzero))
  rewrite *-zeroʳ (VecElem X Idx₁)
        | *-zeroʳ (VecElem X Idx₂)
        | *-oneʳ  (VecElem X Idx₃)
  = refl

VecProduct-LeftIdy≡expected :
  ∀ X k → VecProduct (VecIdy k) X ≡ VecElem X k
VecProduct-LeftIdy≡expected X fzero
  rewrite +-zeroʳ (VecElem X Idx₁)
        | +-zeroʳ (VecElem X Idx₁)
        | +-zeroʳ (VecElem X Idx₁)
  = refl
VecProduct-LeftIdy≡expected X (fsuc fzero)
  rewrite +-zeroʳ (VecElem X Idx₂)
        | +-zeroʳ (VecElem X Idx₂)
  = refl
VecProduct-LeftIdy≡expected X (fsuc (fsuc fzero))
  rewrite +-zeroʳ  (VecElem X Idx₃)
  = refl

-- 3x3 Matrix Identity
MtxIdy : Matrix
MtxIdy =
  VecIdy Idx₁ ∷
  VecIdy Idx₂ ∷
  VecIdy Idx₃ ∷ []

MtxIdy-Row≡expected : ∀ i → MtxRow MtxIdy i ≡ VecIdy i
MtxIdy-Row≡expected fzero
  rewrite Triple-Elem≡expected (MtxRow MtxIdy fzero)
  = refl
MtxIdy-Row≡expected (fsuc fzero)
  rewrite Triple-Elem≡expected (MtxRow MtxIdy (fsuc fzero))
  = refl
MtxIdy-Row≡expected (fsuc (fsuc fzero))
  rewrite Triple-Elem≡expected (MtxRow MtxIdy (fsuc (fsuc fzero)))
  = refl

MtxIdy-Col≡expected : ∀ i → MtxCol MtxIdy i ≡ VecIdy i
MtxIdy-Col≡expected fzero
  rewrite Triple-Elem≡expected (MtxCol MtxIdy fzero)
  = refl
MtxIdy-Col≡expected (fsuc fzero)
  rewrite Triple-Elem≡expected (MtxCol MtxIdy (fsuc fzero))
  = refl
MtxIdy-Col≡expected (fsuc (fsuc fzero))
  rewrite Triple-Elem≡expected (MtxCol MtxIdy (fsuc (fsuc fzero)))
  = refl

MtxProduct-Row-RightIdy≡expected :
  ∀ A i → MtxProduct-Row A MtxIdy i ≡ MtxRow A i
MtxProduct-Row-RightIdy≡expected A i
  rewrite VecProduct-RightIdy≡expected (MtxRow A i) Idx₁
        | VecProduct-RightIdy≡expected (MtxRow A i) Idx₂
        | VecProduct-RightIdy≡expected (MtxRow A i) Idx₃
        | Triple-Elem≡expected (MtxRow A i)
  = refl

MtxProduct-Row-LeftIdy≡expected :
  ∀ A i → MtxProduct-Row MtxIdy A i ≡ MtxRow A i
MtxProduct-Row-LeftIdy≡expected A i
  rewrite MtxIdy-Row≡expected i
        | VecProduct-LeftIdy≡expected (MtxCol A Idx₁) i
        | VecProduct-LeftIdy≡expected (MtxCol A Idx₂) i
        | VecProduct-LeftIdy≡expected (MtxCol A Idx₃) i
        | Triple-Elem≡expected (MtxRow A i)
  = refl

MtxProduct-RightIdy≡expected :
  ∀ A → MtxProduct A MtxIdy ≡ A
MtxProduct-RightIdy≡expected A =
  begin
    MtxProduct A MtxIdy
  ≡⟨⟩
    MtxProduct-Row A MtxIdy Idx₁ ∷
    MtxProduct-Row A MtxIdy Idx₂ ∷
    MtxProduct-Row A MtxIdy Idx₃ ∷ []
  ≡⟨⟩
    {!!}

-- MtxProduct-Row : Matrix → Matrix → Fin 3 → Vec ℕ 3
-- MtxProduct-Row A B i =
--   VecProduct (Row i A) (Col Ind₁ B) ∷
--    ∷
--    ∷ []

-- dot : Vec ℕ 3 → Vec ℕ 3 → ℕ
-- dot xs ys = foldr′ _+_ 0 (zipWith _*_ xs ys)
-- 
-- matMul : Matrix → Matrix → Matrix
-- matMul A B = map (λ row → tabulate (λ j → dot row (Col B j))) A
-- 
-- -- Setup Matrix A
-- Row₁A : Vec ℕ 3
-- Row₁A = 1 ∷ 1 ∷ 1 ∷ []
-- 
-- Row₂A : Vec ℕ 3
-- Row₂A = 0 ∷ 1 ∷ 1 ∷ []
-- 
-- Row₃A : Vec ℕ 3
-- Row₃A = 0 ∷ 0 ∷ 1 ∷ []
-- 
-- A¹ : Matrix
-- A¹ = Row₁A ∷ Row₂A ∷ Row₃A ∷ []
-- 
-- Col₁ : Matrix → Vec ℕ 3
-- Col₁ B = Col B Idx₁
-- 
-- Col₂ : Matrix → Vec ℕ 3
-- Col₂ B = Col B Idx₂
-- 
-- Col₃ : Matrix → Vec ℕ 3
-- Col₃ B = Col B Idx₃
-- 
-- -- Setup ProductA
-- ProductA : Matrix → Matrix
-- ProductA B = matMul A¹ B
-- 
-- ProductA-Row₁ : Matrix → Vec ℕ 3
-- ProductA-Row₁ B =
--   dot Row₁A (Col B Idx₁) ∷
--   dot Row₁A (Col B Idx₂) ∷
--   dot Row₁A (Col B Idx₃) ∷ []
-- 
-- ProductA-Row₂ : Matrix → Vec ℕ 3
-- ProductA-Row₂ B =
--   dot Row₂A (Col₁ B) ∷
--   dot Row₂A (Col₂ B) ∷
--   dot Row₂A (Col₃ B) ∷ []
-- 
-- ProductA-Row₃ : Matrix → Vec ℕ 3
-- ProductA-Row₃ B =
--   dot Row₃A (Col₁ B) ∷
--   dot Row₃A (Col₂ B) ∷
--   dot Row₃A (Col₃ B) ∷ []
-- 
-- ProductAB≡expected : ∀ B → ProductA B ≡
--   ProductA-Row₁ B ∷
--   ProductA-Row₂ B ∷
--   ProductA-Row₃ B ∷ []
-- ProductAB≡expected B = refl
-- 
-- -- Setup Matrix I
-- Vec₁I : Vec ℕ 3
-- Vec₁I = 1 ∷ 0 ∷ 0 ∷ []
-- 
-- Vec₂I : Vec ℕ 3
-- Vec₂I = 0 ∷ 1 ∷ 0 ∷ []
-- 
-- Vec₃I : Vec ℕ 3
-- Vec₃I = 0 ∷ 0 ∷ 1 ∷ []
-- 
-- I : Matrix
-- I = Vec₁I ∷ Vec₂I ∷ Vec₃I ∷ []
-- 
-- ProductAI≡expected : ProductA I ≡ A¹
-- ProductAI≡expected = refl
-- 
-- -- Setup PowerA
-- PowerA : ℕ → Matrix
-- PowerA zero = I
-- PowerA (suc n) = ProductA (PowerA n)
-- 
-- -- Line 
-- -- I : Matrix 3 3
-- -- I =
-- --   ( 1 ∷  0 ∷  0 ∷ []) ∷
-- --   ( 0 ∷  1 ∷  0 ∷ []) ∷
-- --   ( 0 ∷  0 ∷  1 ∷ []) ∷ []
-- -- 
-- -- Tr : ℕ → ℕ
-- -- Tr zero = 0
-- -- Tr (suc n) = Tr n + suc n
-- -- 
-- -- ClosedFormAⁿ : ℕ → Matrix 3 3
-- -- ClosedFormAⁿ n =
-- --   ( 1 ∷  n ∷  (Tr n) ∷ []) ∷
-- --   ( 0 ∷  1 ∷  n      ∷ []) ∷
-- --   ( 0 ∷  0 ∷  1      ∷ []) ∷ []
-- -- 
-- -- A² : Matrix 3 3
-- -- A² =
-- --   ( 1 ∷  2 ∷  3 ∷ []) ∷
-- --   ( 0 ∷  1 ∷  2 ∷ []) ∷
-- --   ( 0 ∷  0 ∷  1 ∷ []) ∷ []
-- -- 
-- -- ProductA²≡expected : ProductA A ≡ A²
-- -- ProductA²≡expected = refl
-- -- 
-- -- PowerA : ℕ → Matrix 3 3
-- -- PowerA zero = I
-- -- PowerA (suc n) = ProductA (PowerA n)
-- -- 
-- -- -- Goal: ClosedFormAⁿ is correct
-- -- 
-- -- closed-form-base :
-- --   ClosedFormAⁿ zero ≡ I
-- -- closed-form-base = refl
-- -- 
-- -- closed-form-step :
-- --   ∀ n → ProductA (ClosedFormAⁿ n) ≡ ClosedFormAⁿ (suc n)
-- -- closed-form-step n =
-- --   begin
-- --     ProductA (ClosedFormAⁿ n)
-- --   ≡⟨⟩
-- --     matMul (ClosedFormAⁿ n) A
-- --   ≡⟨⟩
-- --     ( 1 ∷  (suc n) ∷  (Tr n + suc n) ∷ []) ∷
-- --     ( 0 ∷  1       ∷  (suc n)        ∷ []) ∷
-- --     ( 0 ∷  0       ∷  1              ∷ []) ∷ []
-- --   ≡⟨⟩
-- --     ClosedFormAⁿ (suc n)
-- --   ∎


