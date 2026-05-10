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
  ∀ T →
  VecElem T Idx₁ ∷
  VecElem T Idx₂ ∷
  VecElem T Idx₃ ∷ [] ≡ T
Triple-Elem≡expected (x ∷ y ∷ z ∷ []) = refl

-- Triple Product
VecProduct : Triple → Triple → ℕ
VecProduct X Y =
  (VecElem X Idx₁ * VecElem Y Idx₁) +
  (VecElem X Idx₂ * VecElem Y Idx₂) +
  (VecElem X Idx₃ * VecElem Y Idx₃)

-- Identity Basis Triple
VecIdy : Fin 3 → Triple
VecIdy fzero               = 1 ∷ 0 ∷ 0 ∷ []
VecIdy (fsuc fzero)        = 0 ∷ 1 ∷ 0 ∷ []
VecIdy (fsuc (fsuc fzero)) = 0 ∷ 0 ∷ 1 ∷ []

VecProductIdyʳ≡expected :
  ∀ T k → VecProduct T (VecIdy k) ≡ VecElem T k
VecProductIdyʳ≡expected T fzero
  rewrite *-oneʳ  (VecElem T Idx₁)
        | *-zeroʳ (VecElem T Idx₂)
        | *-zeroʳ (VecElem T Idx₃)
        | +-zeroʳ (VecElem T Idx₁)
        | +-zeroʳ (VecElem T Idx₁)
  = refl
VecProductIdyʳ≡expected T (fsuc fzero)
  rewrite *-zeroʳ (VecElem T Idx₁)
        | *-oneʳ  (VecElem T Idx₂)
        | *-zeroʳ (VecElem T Idx₃)
        | +-zeroʳ (VecElem T Idx₂)
  = refl
VecProductIdyʳ≡expected T (fsuc (fsuc fzero))
  rewrite *-zeroʳ (VecElem T Idx₁)
        | *-zeroʳ (VecElem T Idx₂)
        | *-oneʳ  (VecElem T Idx₃)
  = refl

VecProductIdyˡ≡expected :
  ∀ T k → VecProduct (VecIdy k) T ≡ VecElem T k
VecProductIdyˡ≡expected T fzero
  rewrite +-zeroʳ (VecElem T Idx₁)
        | +-zeroʳ (VecElem T Idx₁)
        | +-zeroʳ (VecElem T Idx₁)
  = refl
VecProductIdyˡ≡expected T (fsuc fzero)
  rewrite +-zeroʳ (VecElem T Idx₂)
        | +-zeroʳ (VecElem T Idx₂)
  = refl
VecProductIdyˡ≡expected T (fsuc (fsuc fzero))
  rewrite +-zeroʳ  (VecElem T Idx₃)
  = refl

-- 3x3 Matrix Type
Matrix : Set
Matrix = Vec Triple 3

-- Matrix Element
MtxElem : Matrix → Fin 3 → Fin 3 → ℕ
MtxElem M i j = VecElem (lookup M i) j

MtxElem≡expected :
  ∀ M →
  (MtxElem M Idx₁ Idx₁ ∷
   MtxElem M Idx₁ Idx₂ ∷
   MtxElem M Idx₁ Idx₃ ∷ []) ∷
  (MtxElem M Idx₂ Idx₁ ∷
   MtxElem M Idx₂ Idx₂ ∷
   MtxElem M Idx₂ Idx₃ ∷ []) ∷
  (MtxElem M Idx₃ Idx₁ ∷
   MtxElem M Idx₃ Idx₂ ∷
   MtxElem M Idx₃ Idx₃ ∷ []) ∷ [] ≡ M
MtxElem≡expected (T₁ ∷ T₂ ∷ T₃ ∷ [])
  rewrite Triple-Elem≡expected T₁
        | Triple-Elem≡expected T₂
        | Triple-Elem≡expected T₃
  = refl

-- Matrix Row
MtxRow : Matrix → Fin 3 → Triple
MtxRow M i =
  MtxElem M i Idx₁ ∷
  MtxElem M i Idx₂ ∷
  MtxElem M i Idx₃ ∷ []

-- Matrix Element By Row Slice
MtxElem-ByRow≡expected :
  ∀ M i j → VecElem (MtxRow M i) j ≡ MtxElem M i j
MtxElem-ByRow≡expected M i fzero               = refl
MtxElem-ByRow≡expected M i (fsuc fzero)        = refl
MtxElem-ByRow≡expected M i (fsuc (fsuc fzero)) = refl

-- Matrix Column
MtxCol : Matrix → Fin 3 → Triple
MtxCol M j =
  MtxElem M Idx₁ j ∷
  MtxElem M Idx₂ j ∷
  MtxElem M Idx₃ j ∷ []

-- Matrix Element By Column Slice
MtxElem-ByCol≡expected :
  ∀ M i j → VecElem (MtxCol M j) i ≡ MtxElem M i j
MtxElem-ByCol≡expected M fzero j               = refl
MtxElem-ByCol≡expected M (fsuc fzero) j        = refl
MtxElem-ByCol≡expected M (fsuc (fsuc fzero)) j = refl

-- Matrix Column By Row Slice
MtxCol-ByRow≡expected :
  ∀ M j →
  VecElem (MtxRow M Idx₁) j ∷
  VecElem (MtxRow M Idx₂) j ∷
  VecElem (MtxRow M Idx₃) j ∷ [] ≡ MtxCol M j
MtxCol-ByRow≡expected M j
  rewrite MtxElem-ByRow≡expected M Idx₁ j
        | MtxElem-ByRow≡expected M Idx₂ j
        | MtxElem-ByRow≡expected M Idx₃ j
  = refl

-- Matrix Row By Column Slice
MtxRow-ByCol≡expected :
  ∀ M i →
  VecElem (MtxCol M Idx₁) i ∷
  VecElem (MtxCol M Idx₂) i ∷
  VecElem (MtxCol M Idx₃) i ∷ [] ≡ MtxRow M i
MtxRow-ByCol≡expected M i
  rewrite MtxElem-ByCol≡expected M i Idx₁
        | MtxElem-ByCol≡expected M i Idx₂
        | MtxElem-ByCol≡expected M i Idx₃
  = refl

-- Matrix Product Element
MtxProduct-Elem :
  Matrix →
  Matrix →
  Fin 3 →
  Fin 3 → ℕ
MtxProduct-Elem A B i j = VecProduct (MtxRow A i) (MtxCol B j)

MtxProduct-Elem≡expected :
  ∀ A B i j →
  MtxProduct-Elem A B i j ≡
    (MtxElem A i Idx₁) * (MtxElem B Idx₁ j) +
    (MtxElem A i Idx₂) * (MtxElem B Idx₂ j) +
    (MtxElem A i Idx₃) * (MtxElem B Idx₃ j)
MtxProduct-Elem≡expected A B i j = refl

-- Matrix Product Row
MtxProduct-Row : Matrix → Matrix → Fin 3 → Triple
MtxProduct-Row A B i =
  VecProduct (MtxRow A i) (MtxCol B Idx₁) ∷
  VecProduct (MtxRow A i) (MtxCol B Idx₂) ∷
  VecProduct (MtxRow A i) (MtxCol B Idx₃) ∷ []

MtxProduct-Row≡expected :
  ∀ A B i →
  MtxProduct-Row A B i ≡
    MtxProduct-Elem A B i Idx₁ ∷
    MtxProduct-Elem A B i Idx₂ ∷
    MtxProduct-Elem A B i Idx₃ ∷ []
MtxProduct-Row≡expected A B i = refl

-- Matrix Product Column
MtxProduct-Col : Matrix → Matrix → Fin 3 → Triple
MtxProduct-Col A B j =
  VecProduct (MtxRow A Idx₁) (MtxCol B j) ∷
  VecProduct (MtxRow A Idx₂) (MtxCol B j) ∷
  VecProduct (MtxRow A Idx₃) (MtxCol B j) ∷ []

MtxProduct-Col≡expected :
  ∀ A B j →
  MtxProduct-Col A B j ≡
    MtxProduct-Elem A B Idx₁ j ∷
    MtxProduct-Elem A B Idx₂ j ∷
    MtxProduct-Elem A B Idx₃ j ∷ []
MtxProduct-Col≡expected A B j = refl

-- Matrix Product
MtxProduct : Matrix → Matrix → Matrix
MtxProduct A B =
  MtxProduct-Row A B Idx₁ ∷
  MtxProduct-Row A B Idx₂ ∷
  MtxProduct-Row A B Idx₃ ∷ []

MtxProduct≡expected :
  ∀ A B →
  MtxProduct A B ≡
  (MtxProduct-Elem A B Idx₁ Idx₁ ∷
   MtxProduct-Elem A B Idx₁ Idx₂ ∷
   MtxProduct-Elem A B Idx₁ Idx₃ ∷ []) ∷
  (MtxProduct-Elem A B Idx₂ Idx₁ ∷
   MtxProduct-Elem A B Idx₂ Idx₂ ∷
   MtxProduct-Elem A B Idx₂ Idx₃ ∷ []) ∷
  (MtxProduct-Elem A B Idx₃ Idx₁ ∷
   MtxProduct-Elem A B Idx₃ Idx₂ ∷
   MtxProduct-Elem A B Idx₃ Idx₃ ∷ []) ∷ []
MtxProduct≡expected A B = refl

-- 3x3 Identity Matrix
MtxIdy : Matrix
MtxIdy =
  VecIdy Idx₁ ∷
  VecIdy Idx₂ ∷
  VecIdy Idx₃ ∷ []

-- Identity Matrix Row
MtxIdy-Row≡expected : ∀ i → MtxRow MtxIdy i ≡ VecIdy i
MtxIdy-Row≡expected fzero
  rewrite Triple-Elem≡expected (MtxRow MtxIdy Idx₁)
  = refl
MtxIdy-Row≡expected (fsuc fzero)
  rewrite Triple-Elem≡expected (MtxRow MtxIdy Idx₂)
  = refl
MtxIdy-Row≡expected (fsuc (fsuc fzero))
  rewrite Triple-Elem≡expected (MtxRow MtxIdy Idx₃)
  = refl

-- Identity Matrix Column
MtxIdy-Col≡expected : ∀ j → MtxCol MtxIdy j ≡ VecIdy j
MtxIdy-Col≡expected fzero
  rewrite Triple-Elem≡expected (MtxCol MtxIdy Idx₁)
  = refl
MtxIdy-Col≡expected (fsuc fzero)
  rewrite Triple-Elem≡expected (MtxCol MtxIdy Idx₂)
  = refl
MtxIdy-Col≡expected (fsuc (fsuc fzero))
  rewrite Triple-Elem≡expected (MtxCol MtxIdy Idx₃)
  = refl

-- Identity Matrix Right Product Element
MtxProductIdyʳ-Elem≡expected :
  ∀ M i j → MtxProduct-Elem M MtxIdy i j ≡ MtxElem M i j
MtxProductIdyʳ-Elem≡expected M i fzero
  rewrite VecProductIdyʳ≡expected (MtxRow M i) Idx₁
        | MtxElem-ByRow≡expected M i Idx₁
  = refl
MtxProductIdyʳ-Elem≡expected M i (fsuc fzero)
  rewrite VecProductIdyʳ≡expected (MtxRow M i) Idx₂
        | MtxElem-ByRow≡expected M i Idx₂
  = refl
MtxProductIdyʳ-Elem≡expected M i (fsuc (fsuc fzero))
  rewrite VecProductIdyʳ≡expected (MtxRow M i) Idx₃
        | MtxElem-ByRow≡expected M i Idx₃
  = refl

-- Identity Matrix Left Product Element
MtxProductIdyˡ-Elem≡expected :
  ∀ M i j → MtxProduct-Elem MtxIdy M i j ≡ MtxElem M i j
MtxProductIdyˡ-Elem≡expected M fzero j
  rewrite VecProductIdyˡ≡expected (MtxCol M j) Idx₁
        | MtxElem-ByCol≡expected M Idx₁ j
  = refl
MtxProductIdyˡ-Elem≡expected M (fsuc fzero) j
  rewrite VecProductIdyˡ≡expected (MtxCol M j) Idx₂
        | MtxElem-ByCol≡expected M Idx₂ j
  = refl
MtxProductIdyˡ-Elem≡expected M (fsuc (fsuc fzero)) j
  rewrite VecProductIdyˡ≡expected (MtxCol M j) Idx₃
        | MtxElem-ByCol≡expected M Idx₃ j
  = refl

-- Identity Matrix Right Product Row
MtxProductIdyʳ-Row≡expected :
  ∀ M i → MtxProduct-Row M MtxIdy i ≡ MtxRow M i
MtxProductIdyʳ-Row≡expected M i
  rewrite MtxProductIdyʳ-Elem≡expected M i Idx₁
        | MtxProductIdyʳ-Elem≡expected M i Idx₂
        | MtxProductIdyʳ-Elem≡expected M i Idx₃
  = refl

-- Identity Matrix Left Product Row
MtxProductIdyˡ-Row≡expected :
  ∀ M i → MtxProduct-Row MtxIdy M i ≡ MtxRow M i
MtxProductIdyˡ-Row≡expected M i
  rewrite MtxProductIdyˡ-Elem≡expected M i Idx₁
        | MtxProductIdyˡ-Elem≡expected M i Idx₂
        | MtxProductIdyˡ-Elem≡expected M i Idx₃
  = refl

-- Identity Matrix Right Product Column
MtxProductIdyʳ-Col≡expected :
  ∀ M j → MtxProduct-Col M MtxIdy j ≡ MtxCol M j
MtxProductIdyʳ-Col≡expected M j
  rewrite MtxProductIdyʳ-Elem≡expected M Idx₁ j
        | MtxProductIdyʳ-Elem≡expected M Idx₂ j
        | MtxProductIdyʳ-Elem≡expected M Idx₃ j
  = refl

-- Identity Matrix Left Product Column
MtxProductIdyˡ-Col≡expected :
  ∀ M j → MtxProduct-Col MtxIdy M j ≡ MtxCol M j
MtxProductIdyˡ-Col≡expected M j
  rewrite MtxProductIdyˡ-Elem≡expected M Idx₁ j
        | MtxProductIdyˡ-Elem≡expected M Idx₂ j
        | MtxProductIdyˡ-Elem≡expected M Idx₃ j
  = refl

-- Identity Matrix Right Product
MtxProductIdyʳ≡expected :
  ∀ M → MtxProduct M MtxIdy ≡ M
MtxProductIdyʳ≡expected M
  rewrite MtxProductIdyʳ-Elem≡expected M Idx₁ Idx₁
        | MtxProductIdyʳ-Elem≡expected M Idx₁ Idx₂
        | MtxProductIdyʳ-Elem≡expected M Idx₁ Idx₃
        | MtxProductIdyʳ-Elem≡expected M Idx₂ Idx₁
        | MtxProductIdyʳ-Elem≡expected M Idx₂ Idx₂
        | MtxProductIdyʳ-Elem≡expected M Idx₂ Idx₃
        | MtxProductIdyʳ-Elem≡expected M Idx₃ Idx₁
        | MtxProductIdyʳ-Elem≡expected M Idx₃ Idx₂
        | MtxProductIdyʳ-Elem≡expected M Idx₃ Idx₃
        | MtxElem≡expected M
  = refl

-- Identity Matrix Left Product
MtxProductIdyˡ≡expected :
  ∀ M → MtxProduct MtxIdy M ≡ M
MtxProductIdyˡ≡expected M
  rewrite MtxProductIdyˡ-Elem≡expected M Idx₁ Idx₁
        | MtxProductIdyˡ-Elem≡expected M Idx₁ Idx₂
        | MtxProductIdyˡ-Elem≡expected M Idx₁ Idx₃
        | MtxProductIdyˡ-Elem≡expected M Idx₂ Idx₁
        | MtxProductIdyˡ-Elem≡expected M Idx₂ Idx₂
        | MtxProductIdyˡ-Elem≡expected M Idx₂ Idx₃
        | MtxProductIdyˡ-Elem≡expected M Idx₃ Idx₁
        | MtxProductIdyˡ-Elem≡expected M Idx₃ Idx₂
        | MtxProductIdyˡ-Elem≡expected M Idx₃ Idx₃
        | MtxElem≡expected M
  = refl

-- Matrix Power
MtxPower : Matrix → ℕ → Matrix
MtxPower M zero = MtxIdy -- For ℕ > 0, encountered on the right
MtxPower M (suc n) = MtxProduct M (MtxPower M n)

-- Triangular Number
Tr : ℕ → ℕ
Tr zero = zero
Tr (suc n) = (suc n) + (Tr n)

Tr≡expected : ∀ n → (Tr n) + n + 1 ≡ Tr (suc n)
Tr≡expected n
  rewrite +-oneʳ (Tr n + n)
        | symm-sum (Tr n) n
  = refl

-- 3x3 Accumulator Matrix
MtxAcc : Matrix
MtxAcc =
  (1 ∷ 1 ∷ 1 ∷ []) ∷
  (0 ∷ 1 ∷ 1 ∷ []) ∷
  (0 ∷ 0 ∷ 1 ∷ []) ∷ []

-- Closed Form Target
Acc : ℕ → Matrix
Acc n =
  (1 ∷ n ∷ Tr n ∷ []) ∷
  (0 ∷ 1 ∷ n    ∷ []) ∷
  (0 ∷ 0 ∷ 1    ∷ []) ∷ []


-- To Show: ∀ n → MtxPower MtxAcc n ≡ Acc n
Acc⁰≡expected : Acc zero ≡ MtxIdy
Acc⁰≡expected = refl

Acc¹≡expected : Acc (suc zero) ≡ MtxAcc
Acc¹≡expected = refl

-- Accumulator Product Element
MtxProductAcc-Elem≡expected :
  ∀ n i j →
  MtxProduct-Elem MtxAcc (Acc n) i j ≡ MtxElem (Acc (suc n)) i j
MtxProductAcc-Elem≡expected n fzero fzero = refl
MtxProductAcc-Elem≡expected n fzero (fsuc fzero)
  rewrite MtxProduct-Elem≡expected MtxAcc (Acc n) Idx₁ Idx₂
        | +-zeroʳ n
        | +-zeroʳ (n + 1)
        | +-oneʳ n
  = refl
MtxProductAcc-Elem≡expected n fzero (fsuc (fsuc fzero))
  rewrite MtxProduct-Elem≡expected MtxAcc (Acc n) Idx₁ Idx₃
        | +-zeroʳ n
        | +-zeroʳ (Tr n)
        | suc-sumˡ n (Tr n)
        | Tr≡expected n
  = refl
MtxProductAcc-Elem≡expected n (fsuc fzero) fzero = refl
MtxProductAcc-Elem≡expected n (fsuc fzero) (fsuc fzero) = refl
MtxProductAcc-Elem≡expected n (fsuc fzero) (fsuc (fsuc fzero))
  rewrite MtxProduct-Elem≡expected MtxAcc (Acc n) Idx₂ Idx₃
        | +-zeroʳ n
        | +-oneʳ n
  = refl
MtxProductAcc-Elem≡expected n (fsuc (fsuc fzero)) fzero = refl
MtxProductAcc-Elem≡expected n (fsuc (fsuc fzero)) (fsuc fzero) = refl
MtxProductAcc-Elem≡expected n (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = refl

-- Accumulator Product
MtxProductAcc≡expected :
  ∀ n → MtxProduct MtxAcc (Acc n) ≡ Acc (suc n)
MtxProductAcc≡expected n
  rewrite MtxProductAcc-Elem≡expected n Idx₁ Idx₁
        | MtxProductAcc-Elem≡expected n Idx₁ Idx₂
        | MtxProductAcc-Elem≡expected n Idx₁ Idx₃
        | MtxProductAcc-Elem≡expected n Idx₂ Idx₁
        | MtxProductAcc-Elem≡expected n Idx₂ Idx₂
        | MtxProductAcc-Elem≡expected n Idx₂ Idx₃
        | MtxProductAcc-Elem≡expected n Idx₃ Idx₁
        | MtxProductAcc-Elem≡expected n Idx₃ Idx₂
        | MtxProductAcc-Elem≡expected n Idx₃ Idx₃
        | MtxElem≡expected (Acc (suc n))
  = refl

-- Accumulator Power
MtxPowerAcc≡expected :
  ∀ n → MtxPower MtxAcc n ≡ Acc n
MtxPowerAcc≡expected zero
  rewrite Acc⁰≡expected = refl
MtxPowerAcc≡expected (suc n)
  rewrite MtxPowerAcc≡expected n
        | MtxProductAcc≡expected n
  = refl
