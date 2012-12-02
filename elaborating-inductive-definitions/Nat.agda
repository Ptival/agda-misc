module Nat where

open import Enumeration
open import InductiveTypes

{-
Nat ≔ μ ( F(X) = 1 + X )
-}

NatE : EnumU
NatE = (consE (` "O") (consE (` "S") nilE))

NatF : EnumT NatE → Desc
NatF (`0   .(` "O") .(consE (` "S") nilE))   = `1
NatF (`1+_ .(` "O") .(consE (` "S") nilE) x) = `var

NatD : Desc
NatD = `σ NatE NatF

Nat : Set
Nat = μ NatD
