module InductiveTypes where

open import Data.Product
open import Data.Unit

open import Enumeration

data Desc : Set₁ where
  `var : Desc
  `1 : Desc
  _`×_ : (A : Desc) → (B : Desc) → Desc
  `Π : (S : Set) → (T : S → Desc) → Desc
  `Σ : (S : Set) → (T : S → Desc) → Desc
  `σ : (E : EnumU) → (T : EnumT E → Desc) → Desc

⟦_⟧ : Desc → Set → Set
⟦ `var ⟧   X = X
⟦ `1 ⟧     X = Unit
⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦ `Π S T ⟧ X = (s : S) → ⟦ T s ⟧ X
⟦ `Σ S T ⟧ X = Σ S (λ s → ⟦ T s ⟧ X)
⟦ `σ E T ⟧ X = Σ (EnumT E) (λ e → ⟦ T e ⟧ X)

data μ (D : Desc) : Set where
  μin : ⟦ D ⟧ (μ D) → μ D

All : (D : Desc) (X : Set) (P : X → Set) → ⟦ D ⟧ X → Set
All `var     X P x               = P x
All `1       X P x               = Unit
All (A `× B) X P (proj₁ , proj₂) = All A X P proj₁ × All B X P proj₂
All (`Π S T) X P f               = (s : S) → All (T s) X P (f s)
All (`Σ S T) X P (proj₁ , proj₂) = All (T proj₁) X P proj₂
All (`σ E T) X P (proj₁ , proj₂) = All (T proj₁) X P proj₂

all : (D : Desc) (X : Set) (P : X → Set) (R : (x : X) → P x) (x : ⟦ D ⟧ X) → All D X P x
all `var     X P R x               = R x
all `1       X P R x               = unit
all (A `× B) X P R (proj₁ , proj₂) = all A X P R proj₁ , all B X P R proj₂
all (`Π S T) X P R f               = λ s → all (T s) X P R (f s)
all (`Σ S T) X P R (proj₁ , proj₂) = all (T proj₁) X P R proj₂
all (`σ E T) X P R (proj₁ , proj₂) = all (T proj₁) X P R proj₂

{-
Termination checker fails on:

induction :
  (D : Desc)
  (P : μ D → Set)
  (m : (d : ⟦ D ⟧ (μ D)) → All D (μ D) P d → P (μin d))
  (x : μ D) → P x
induction D P m (μin x) = I x (all D (μ D) P (λ x → induction D P m x) x)
-}

module Elim
  (D : Desc)
  (P : μ D -> Set)
  (m : (d : ⟦ D ⟧ (μ D)) → All D (μ D) P d → P (μin d))
  where

  mutual
    induction : (x : μ D) → P x
    induction (μin xs) = m xs (hyps D xs)

    hyps : (D' : Desc) -> (xs : ⟦ D' ⟧ (μ D)) -> All D' (μ D) P xs
    hyps `var     x               = induction x
    hyps `1       x               = unit
    hyps (A `× B) (proj₁ , proj₂) = hyps A proj₁ , hyps B proj₂
    hyps (`Π S T) f               = λ s → hyps (T s) (f s)
    hyps (`Σ S T) (proj₁ , proj₂) = hyps (T proj₁) proj₂
    hyps (`σ E T) (proj₁ , proj₂) = hyps (T proj₁) proj₂

induction :
  (D : Desc)
  (P : μ D → Set)
  (m : (d : ⟦ D ⟧ (μ D)) → All D (μ D) P d → P (μin d))
  (x : μ D) → P x
induction = Elim.induction
