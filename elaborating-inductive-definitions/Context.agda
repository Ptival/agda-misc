module Context where

mutual

data Context : Set where
  ∅ : Context
  _,_∷_ : Context → Context → Context
