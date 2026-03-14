module Artin-1-2 where

open import MatrixMul
open import Agda.Builtin.FromNat
open import Data.Vec using ([]; _∷_)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

AaBa : Matrix 2 2
AaBa = matMul Aa Ba

BaAa : Matrix 3 3
BaAa = matMul Ba Aa

AbBb : Matrix 2 2
AbBb = matMul Ab Bb

BbAb : Matrix 2 2
BbAb = matMul Bb Ab

AbBb-expected : Matrix 2 2
AbBb-expected = (ℤ.pos 18 ∷ ℤ.pos 4 ∷ []) ∷
                (ℤ.pos 12 ∷ ℤ.pos 0 ∷ []) ∷
                []

AbBb-actual : AbBb ≡ AbBb-expected
AbBb-actual = refl
