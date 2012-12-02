module Vector where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Enumeration
open import InductiveFamilies

module VectorCoq where

  VecE : EnumU
  VecE = consE (`"Nil") (consE (`"Cons") nilE)

  VecF : (A : Set) → (n : ℕ) → EnumT VecE → IDesc ℕ
  VecF A n (`0   .(` "Nil") .(consE (` "Cons") nilE))   = `Σ (n ≡ 0) (λ _ → `1)
  VecF A n (`1+_ .(` "Nil") .(consE (` "Cons") nilE) x) = `Σ ℕ (λ m → `Σ (n ≡ suc m) (λ _ → `Σ A (λ _ → `var m)))

  VecD : (A : Set) (n : ℕ) → IDesc ℕ
  VecD A n = `σ VecE (VecF A n)

  Vec : (A : Set) (n : ℕ) → Set
  Vec A n = μ (VecD A) n

module VectorAlt where

  VecE : EnumU
  VecE = consE (`"Nil") (consE (`"Cons") nilE)

  VecF : (A : Set) → (n : ℕ) → EnumT VecE → IDesc ℕ
  VecF A zero    x = `1
  VecF A (suc n) x = `Σ A (λ _ → `var n)

  VecD : (A : Set) (n : ℕ) → IDesc ℕ
  VecD A n = `σ VecE (VecF A n)

  Vec : (A : Set) (n : ℕ) → Set
  Vec A n = μ (VecD A) n
