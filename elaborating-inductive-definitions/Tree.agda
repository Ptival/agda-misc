module Tree where

open import Enumeration
open import InductiveTypes

{-
Tree ≔ μ ( Tᴬ(X) = 1 + A × X² )
-}

TreeE : EnumU
TreeE = (consE (` "Leaf") (consE (` "Node") nilE))

TreeF : (A : Set) → EnumT TreeE → Desc
TreeF A (`0   .(` "Leaf") .(consE (` "Node") nilE))   = `1
TreeF A (`1+_ .(` "Leaf") .(consE (` "Node") nilE) x) = `var `× `Σ A (λ _ → `var)

TreeD : (A : Set) → Desc
TreeD A = `σ TreeE (TreeF A)

Tree : (A : Set) → Set
Tree A = μ (TreeD A)
