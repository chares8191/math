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

ABpart : Matrix 2 3
ABpart = matMul A B

AB-expected : Matrix 2 3
AB-expected = (ℤ.pos 2 ∷ ℤ.pos 3 ∷ ℤ.pos 8 ∷ []) ∷
              (ℤ.pos 1 ∷ ℤ.pos 1 ∷ ℤ.pos 3 ∷ []) ∷
              []

AB-actual : ABpart ≡ AB-expected
AB-actual = refl

BCpart : Matrix 2 1
BCpart = matMul B C

BC-expected : Matrix 2 1
BC-expected = (ℤ.pos 10 ∷ []) ∷
              (ℤ.pos 14 ∷ []) ∷
              []

BC-actual : BCpart ≡ BC-expected
BC-actual = refl

ABC-expected : Matrix 2 1
ABC-expected = (ℤ.pos 38 ∷ []) ∷
               (ℤ.pos 14 ∷ []) ∷
               []

ABpartC : Matrix 2 1
ABpartC = matMul ABpart C

ABCpart : Matrix 2 1
ABCpart = matMul A BCpart

ABpartC-actual : ABpartC ≡ ABC-expected
ABpartC-actual = refl

ABCpart-actual : ABCpart ≡ ABC-expected
ABCpart-actual = refl

ABCassc-actual : ABpartC ≡ ABCpart
ABCassc-actual = refl

