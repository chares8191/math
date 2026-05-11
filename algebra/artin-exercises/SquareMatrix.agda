module SquareMatrix where

open import NatHelpers
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec using (Vec; []; _∷_; lookup)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)

Tuple : ℕ → Set
Tuple k = Vec ℕ k

Square : ℕ → Set
Square k = Vec (Tuple k) k

TupleLookup :
  ∀ {k} → Tuple k → Fin k → ℕ
TupleLookup (head ∷ tail) fzero = head
TupleLookup (head ∷ tail) (fsuc k) = TupleLookup tail k

TupleProduct :
  ∀ {k} → Tuple k → Tuple k → ℕ
TupleProduct [] [] = zero
TupleProduct (headˡ ∷ tailˡ) (headʳ ∷ tailʳ)
  = headˡ * headʳ + TupleProduct tailˡ tailʳ

MatrixLookup :
  ∀ {rows cols} →
  Vec (Tuple cols) rows →
  Fin rows →
  Tuple cols
MatrixLookup (head ∷ tail) fzero = head
MatrixLookup (head ∷ tail) (fsuc k) = MatrixLookup tail k

module SquareMatrix (N : ℕ) where
  Index : Set
  Index = Fin N

  Vector : Set
  Vector = Tuple N

  Matrix : Set
  Matrix = Square N

  -- Vector Element
  VectorElement : Vector → Index → ℕ
  VectorElement V k = TupleLookup V k

  

  

  
