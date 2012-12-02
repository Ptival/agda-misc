module TypeSynthesis where

open import Data.Nat
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality

↑_ : Level.Level → Level.Level
↑_ = Level.suc

mutual

  data _Inf⟶_∈_ {k : Level} : Set k → Set k → Set (↑ k) → Set (↑ k) where
    Syn2 : {S : Set (↑ k)}{x : S} → x Inf⟶ x ∈ S

  data _∋_Chk⟶_ {k : Level} : Set (↑ ↑ k) → Set (↑ k) → Set (↑ k) → Set (↑ k) where
    ChkSet : Set (↑ k) ∋ Set k Chk⟶ Set k

