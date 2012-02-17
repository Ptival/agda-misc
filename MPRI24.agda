module MPRI24 where

open import Data.Empty
open import Data.Nat using (ℕ)
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module CBV-SOS where

  infixl 2 _$_
  infix 1 _⟶_

  Var : Set
  Var = String

  data Term : Set where
    C : (n : ℕ) → Term
    V : (x : Var) → Term
    ƛ_↦_ : (x : Var) → (e : Term) → Term
    _$_ : (f : Term) → (g : Term) → Term

  data Value : Term -> Set where
    VC : ∀ n → Value (C n)
    Vƛ : ∀ x a → Value (ƛ x ↦ a)

  _[_←_] : Term → Var → Term → Term
  C n [ x ← v ] = C n
  V x [ x' ← v ] with x ≟ x'
  V .x' [ x' ← v ] | yes refl = v
  V x [ x' ← v ] | no ¬p = V x
  (ƛ x ↦ e) [ x' ← v ] with x ≟ x'
  (ƛ .x' ↦ e) [ x' ← v ] | yes refl = ƛ x' ↦ e
  (ƛ x ↦ e) [ x' ← v ] | no ¬p = ƛ x ↦ (e [ x' ← v ])
  (f $ g) [ x ← v ] = f [ x ← v ] $ g [ x ← v ]

  data _⟶_ : Term → Term → Set where
    β : ∀ x a v → Value v → (ƛ x ↦ a) $ v ⟶ a [ x ← v ]
    ⟶$ : ∀ {a a'} b → a ⟶ a' → a $ b ⟶ a' $ b
    $⟶ : ∀ {b b'} v → Value v → b ⟶ b' → v $ b ⟶ v $ b'

  reduction-example :
    (ƛ "x" ↦ ƛ "y" ↦ (V "y" $ V "x")) $ ((ƛ "x" ↦ V "x") $ C 1) $ (ƛ "x" ↦ V "x")
    ⟶
    (ƛ "x" ↦ ƛ "y" ↦ (V "y" $ V "x")) $ C 1 $ (ƛ "x" ↦ V "x")
  reduction-example =
    ⟶$ (ƛ "x" ↦ V "x")
    ($⟶ (ƛ "x" ↦ ƛ "y" ↦ (V "y" $ V "x")) (Vƛ "x" (ƛ "y" ↦ (V "y" $ V "x")))
    (β "x" (V "x") (C 1) (VC 1)))

  ¬Value⟶ : ∀ v t → Value v → ¬(v ⟶ t)
  ¬Value⟶ .(C n) t (VC n) ()
  ¬Value⟶ .(ƛ x ↦ a) t (Vƛ x a) ()

  ¬ƛ⟶ : ∀ x e t → ¬((ƛ x ↦ e) ⟶ t)
  ¬ƛ⟶ x e t ()

  {- dafuq did I just write?
  weak-reduction : ∀ a a' x → ¬(a ⟶ a' → (ƛ x ↦ a) ⟶ (ƛ x ↦ a'))
  weak-reduction (C n) a' x f = {!!}
  weak-reduction (V x) a' x' f = {!!}
  weak-reduction (ƛ x ↦ e) a' x' f = {!!}
  weak-reduction (f $ g) a' x f' = {!!}
  -}

  {- 1AM, I have no idea what I'm doing! -}
  call-by-value : ∀ x a e v t → (ƛ x ↦ a) $ e ⟶ t → e ⟶ v → Value v
  call-by-value x a
    .(ƛ x' ↦ a' $ v)
    .(a' [ x' ← v ])
    .(a [ x ← ƛ x' ↦ a' $ v ])
    (β .x .a .(ƛ x' ↦ a' $ v) ())
    (β x' a' v y')
  call-by-value x a
    .(ƛ x' ↦ a0 $ v)
    .(a0 [ x' ← v ])
    .(a' $ (ƛ x' ↦ a0 $ v))
    (⟶$ {.(ƛ x ↦ a)} {a'} .(ƛ x' ↦ a0 $ v) ())
    (β x' a0 v y')
  call-by-value x a
    .(ƛ x' ↦ a' $ v)
    .(a' [ x' ← v ])
    .(ƛ x ↦ a $ b')
    ($⟶ {.(ƛ x' ↦ a' $ v)} {b'} .(ƛ x ↦ a) y y')
    (β x' a' v y0)
    = {!!}
  call-by-value x a
    .(a' $ b)
    .(a0 $ b)
    t
    red1
    (⟶$ {a'} {a0} b y)
    = {!!}
  call-by-value x a
    .(v $ b)
    .(v $ b')
    t
    red1
    ($⟶ {b} {b'} v y y')
    = {!!}
