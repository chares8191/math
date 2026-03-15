module MatrixMul where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Literals as ℕL
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec using (Vec; []; _∷_; map; zipWith; foldr′; tabulate; lookup)
open import Data.Integer using (ℤ; _+_; _*_; 0ℤ)
open import Data.Integer.Literals as ℤL
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

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

dot :
  ∀ {n} →
  Vec ℤ n →
  Vec ℤ n →
  ℤ
dot xs ys =
  foldr′ _+_ 0ℤ (zipWith _*_ xs ys)

col :
  ∀ {m n} →
  Fin n →
  Matrix m n →
  Vec ℤ m
col j mat =
  map (λ row → lookup row j) mat

matMul :
  ∀ {m n p} →
  Matrix m n →
  Matrix n p →
  Matrix m p
matMul A B =
  map (λ row → tabulate (λ j → dot row (col j B))) A

identity : ∀ {n} → Matrix n n
identity {n} =
  tabulate λ i →
  tabulate λ j →
  entry i j where
    entry : Fin n → Fin n → ℤ
    entry i j with i ≟ j
    ... | yes _ = ℤ.pos 1
    ... | no  _ = 0ℤ

matPow :
  ∀ {n} →
  ℕ →
  Matrix n n →
  Matrix n n
matPow zero M    = identity
matPow (suc k) M = matMul M (matPow k M)
