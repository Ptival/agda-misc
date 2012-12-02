module InductiveFamilies where

open import Data.Product
open import Data.Unit

open import Enumeration

data IDesc (I : Set) : Set₁ where
  `var : (i : I) → IDesc I
  `1 : IDesc I
  _`×_ : (A : IDesc I) → (B : IDesc I) → IDesc I
  `Π : (S : Set) → (T : S → IDesc I) → IDesc I
  `Σ : (S : Set) → (T : S → IDesc I) → IDesc I
  `σ : (E : EnumU) → (T : EnumT E → IDesc I) → IDesc I

⟦_⟧ : {I : Set} → IDesc I → (I → Set) → Set
⟦ `var i ⟧ X = X i
⟦ `1 ⟧     X = Unit
⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦ `Π S T ⟧ X = (s : S) → ⟦ T s ⟧ X
⟦ `Σ S T ⟧ X = Σ S (λ s → ⟦ T s ⟧ X)
⟦ `σ E T ⟧ X = Σ (EnumT E) (λ e → ⟦ T e ⟧ X)

data μ {I} (fD : I → IDesc I) (i : I) : Set where
  μin : ⟦ fD i ⟧ (λ j → μ fD j) → μ fD i

All : {I : Set} (D : IDesc I) (P : I → Set) → ⟦ D ⟧ P → IDesc (Σ I P)
All (`var i) P x               = `var (i , x)
All `1       P x               = `1
All (A `× B) P (proj₁ , proj₂) = All A P proj₁ `× All B P proj₂
All (`Π S T) P f               = `Π S (λ s → All (T s) P (f s))
All (`Σ S T) P (proj₁ , proj₂) = All (T proj₁) P proj₂
All (`σ E T) P (proj₁ , proj₂) = All (T proj₁) P proj₂

all : {I : Set} (D : IDesc I) (X : I → Set) (R : Σ I X → Set) (P : (x : Σ I X) → R x) (xs : ⟦ D ⟧ X) → ⟦ All D X xs ⟧ R
all (`var i) X R P x               = P (i , x)
all `1       X R P k               = unit
all (A `× B) X R P (proj₁ , proj₂) = all A X R P proj₁ , all B X R P proj₂
all (`Π S T) X R P f               = λ a → all (T a) X R P (f a)
all (`Σ S T) X R P (proj₁ , proj₂) = all (T proj₁) X R P proj₂
all (`σ E T) X R P (proj₁ , proj₂) = all (T proj₁) X R P proj₂

{-
Termination checker fails on:

induction : {I : Set}
  (R : I → IDesc I)
  (P : Σ I (μ R) → Set)
  (m : (i : I) (xs : ⟦ R i ⟧ (μ R)) → ⟦ All (R i) (μ R) xs ⟧ P → P (i , μin xs))
  (i : I) (x : μ R i) → P (i , x)
induction {I} R P m i (μin xs) = m i xs (all (R i) (μ R) P induct xs)
  where
    induct : (x : Σ I (μ R)) → P x
    induct (i , xs) = induction R P m i xs
-}

module Elim {I : Set}
  (R : I -> IDesc I)
  (P : Σ I (μ R) -> Set)
  (m : (i : I) (xs : ⟦ R i ⟧ (μ R)) (hs : ⟦ All (R i) (μ R) xs ⟧ P) -> P (i , μin xs))
  where

  mutual
    induction : (i : I) (x : μ R i) → P (i , x)
    induction i (μin xs) = m i xs (hyps (R i) xs)

    hyps : (D : IDesc I) -> (xs : ⟦ D ⟧ (μ R)) -> ⟦ All D (μ R) xs ⟧ P
    hyps (`var i) x               = induction i x
    hyps `1       x               = unit
    hyps (A `× B) (proj₁ , proj₂) = hyps A proj₁ , hyps B proj₂
    hyps (`Π S T) f               = λ s → hyps (T s) (f s)
    hyps (`Σ S T) (proj₁ , proj₂) = hyps (T proj₁) proj₂
    hyps (`σ E T) (proj₁ , proj₂) = hyps (T proj₁) proj₂

induction : {I : Set}
  (R : I → IDesc I)
  (P : Σ I (μ R) → Set)
  (m : (i : I) (xs : ⟦ R i ⟧ (μ R)) → ⟦ All (R i) (μ R) xs ⟧ P → P (i , μin xs))
  (i : I) (x : μ R i) → P (i , x)
induction = Elim.induction
