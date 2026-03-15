module Artin-1-5 where

open import MatrixMul
open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≤?_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module MatrixProduct (r s t : ℕ) where

  Product : (Left : Matrix r s) -> (Right : Matrix s t) -> Matrix r t
  Product Left Right = matMul Left Right
  
  Cost : (Left : Matrix r s) -> (Right : Matrix s t) → ℕ
  Cost Left Right = r * s * t

module MatrixTripleProduct (l m n p : ℕ) where

  module InnerLeft = MatrixProduct l m n
  module OuterLeft = MatrixProduct l n p

  module InnerRight = MatrixProduct m n p
  module OuterRight = MatrixProduct l m p

  ProductLeft :
    (A : Matrix l m) →
    (B : Matrix m n) →
    (C : Matrix n p) →
    Matrix l p
  ProductLeft A B C = OuterLeft.Product (InnerLeft.Product A B) C

  ProductLeft≡expected :
    (A : Matrix l m) (B : Matrix m n) (C : Matrix n p) →
    ProductLeft A B C ≡ matMul (matMul A B) C
  ProductLeft≡expected A B C = refl

  ProductRight :
    (A : Matrix l m) →
    (B : Matrix m n) →
    (C : Matrix n p) →
    Matrix l p
  ProductRight A B C = OuterRight.Product A (InnerRight.Product B C)

  ProductRight≡expected :
    (A : Matrix l m) (B : Matrix m n) (C : Matrix n p) →
    ProductRight A B C ≡ matMul A (matMul B C)
  ProductRight≡expected A B C = refl

  CostLeft :
    (A : Matrix l m) →
    (B : Matrix m n) →
    (C : Matrix n p) →
    ℕ
  CostLeft A B C =
    InnerLeft.Cost A B +
    OuterLeft.Cost (InnerLeft.Product A B) C

  CostLeft≡expected :
    (A : Matrix l m) (B : Matrix m n) (C : Matrix n p) →
    CostLeft A B C ≡ l * m * n + l * n * p
  CostLeft≡expected A B C = refl

  CostRight :
    (A : Matrix l m) →
    (B : Matrix m n) →
    (C : Matrix n p) →
    ℕ
  CostRight A B C =
    InnerRight.Cost B C +
    OuterRight.Cost A (InnerRight.Product B C)

  CostRight≡expected :
    (A : Matrix l m) (B : Matrix m n) (C : Matrix n p) →
    CostRight A B C ≡ m * n * p + l * m * p
  CostRight≡expected A B C = refl
    
