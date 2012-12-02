module Enumeration where

open import Data.Nat
open import Data.String

data UId : Set where
  `_ : String → UId

data EnumU : Set where
  nilE  : EnumU
  consE : UId → EnumU → EnumU

data EnumT : EnumU → Set where
  `0 : (t : UId) → (E : EnumU) → EnumT (consE t E)
  `1+_ : (t : UId) → (E : EnumU) → ℕ → EnumT (consE t E)
