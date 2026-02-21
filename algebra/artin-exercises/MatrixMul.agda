module MatrixMul where

open import Data.Nat using (ℕ)
import Data.Nat.Literals as ℕL
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; map; zipWith; foldr′; tabulate; lookup)
open import Data.Integer using (ℤ; _+_; _*_; 0ℤ)
open import Data.Integer.Literals as ℤL
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

instance
  tt-instance : ⊤
  tt-instance = tt

  numberℕ : Number ℕ
  numberℕ = ℕL.number

  numberℤ : Number ℤ
  numberℤ = ℤL.number

  negativeℤ : Negative ℤ
  negativeℤ = ℤL.negative

Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vec ℤ n) m

dot : ∀ {n} → Vec ℤ n → Vec ℤ n → ℤ
dot xs ys = foldr′ _+_ 0ℤ (zipWith _*_ xs ys)

col : ∀ {m n} → Fin n → Matrix m n → Vec ℤ m
col j mat = map (λ row → lookup row j) mat

matMul : ∀ {m n p} → Matrix m n → Matrix n p → Matrix m p
matMul A B = map (λ row → tabulate (λ j → dot row (col j B))) A

-- [Artin1.2]
Aa : Matrix 2 3
Aa = (ℤ.pos 1 ∷ ℤ.pos 2 ∷ ℤ.pos 3 ∷ []) ∷
     (ℤ.pos 3 ∷ ℤ.pos 3 ∷ ℤ.pos 1 ∷ []) ∷
     []

Ab : Matrix 2 2
Ab = (ℤ.pos 1 ∷ ℤ.pos 4 ∷ []) ∷
     (ℤ.pos 1 ∷ ℤ.pos 2 ∷ []) ∷
     []

Ba : Matrix 3 2
Ba = (ℤ.negsuc 7  ∷ ℤ.negsuc 3 ∷ []) ∷
     (ℤ.pos 9     ∷ ℤ.pos 5    ∷ []) ∷
     (ℤ.negsuc 2  ∷ ℤ.negsuc 1 ∷ []) ∷
     []

Bb : Matrix 2 2
Bb = (ℤ.pos 6 ∷ ℤ.negsuc 3 ∷ []) ∷
     (ℤ.pos 3 ∷ ℤ.pos 2    ∷ []) ∷
     []

AaBa = matMul Aa Ba
BaAa = matMul Ba Aa
AbBb = matMul Ab Bb
BbAb = matMul Bb Ab

AbBb-expected : Matrix 2 2
AbBb-expected = (ℤ.pos 18 ∷ ℤ.pos 4 ∷ []) ∷
                (ℤ.pos 12 ∷ ℤ.pos 0 ∷ []) ∷
                []

AbBb-actual : AbBb ≡ AbBb-expected
AbBb-actual = refl
