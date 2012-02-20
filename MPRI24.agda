module MPRI24 where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Relation.Nullary using (¬_; yes; no)

module CBV-SOS where

  Var : Set
  Var = String

  infixl 2 _$_
  data Term : Set where
    C : (n : ℕ) → Term
    V : (x : Var) → Term
    ƛ : (x : Var) → (e : Term) → Term
    _$_ : (f : Term) → (g : Term) → Term

  data Value : Term → Set where
    VC : ∀ n → Value (C n)
    Vƛ : ∀ x a → Value (ƛ x a)

  _[_←_] : ∀ {v} → Term → Var → Value v → Term
  C n [ x ← v' ] = C n
  V x [ x' ← v' ] with x ≟ x'
  V .x' [ x' ← VC n ] | yes refl = C n
  V .x' [ x' ← Vƛ x a ] | yes refl = ƛ x a
  V x [ x' ← v' ] | no ¬p = V x
  (ƛ x e) [ x' ← v' ] with x ≟ x'
  (ƛ .x' e) [ x' ← v' ] | yes refl = ƛ x' e
  (ƛ x e) [ x' ← v' ] | no ¬p = ƛ x (e [ x' ← v' ])
  (f $ g) [ x ← v' ] = f [ x ← v' ] $ g [ x ← v' ]

  infix 1 _⟶_
  data _⟶_ : Term → Term → Set where
    β : ∀ x a {v} → (vv : Value v)         → (ƛ x a) $ v ⟶ a [ x ← vv ]
    ⟶$ : ∀ {a a'} b → a ⟶ a'             →         a $ b ⟶ a' $ b
    $⟶ : ∀ {b b' v} → Value v → (b ⟶ b') →         v $ b ⟶ v $ b'

  reduction-example :
    (ƛ "x" (ƛ "y" (V "y" $ V "x"))) $ ((ƛ "x" (V "x")) $ C 1) $ (ƛ "x" (V "x"))
    ⟶
    (ƛ "x" (ƛ "y" (V "y" $ V "x"))) $ C 1 $ (ƛ "x" (V "x"))
  reduction-example =
    ⟶$ (ƛ "x" (V "x"))
    ($⟶ (Vƛ "x" (ƛ "y" (V "y" $ V "x")))
    (β "x" (V "x") (VC 1)))

  ¬Value⟶ : ∀ {v t} → Value v → ¬(v ⟶ t)
  ¬Value⟶ {.(C n)} {t} (VC n) ()
  ¬Value⟶ {.(ƛ x a)} {t} (Vƛ x a) ()

  -- just a special case of ¬Value⟶
  weak-reduction : ∀ x e t → ¬((ƛ x e) ⟶ t)
  weak-reduction x e t ()

  {-
  By construction, β-reduction only happens once the argument has been fully
  reduced to a value.
  -}
  call-by-value : ∀ x a v → (vv : Value v) →
    ((ƛ x a) $ v ⟶ a [ x ← vv ]) → Value v
  call-by-value x a v vv red = vv

  left-to-right : ∀ v b b' → b ≢ b' → (b ⟶ b') → (v $ b ⟶ v $ b') → Value v
  left-to-right (C n) b b' b≢b' red1 red2 = VC n
  left-to-right (V x) .b' b' b≢b' red1 (⟶$ .b' ())
  left-to-right (V x) b b' b≢b' red1 ($⟶ () y')
  left-to-right (ƛ x e) b b' b≢b' red1 red2 = Vƛ x e
  left-to-right (f $ g) .b' b' b≢b' red1 (⟶$ .b' y) = ⊥-elim (b≢b' refl)
  left-to-right (f $ g) b b' b≢b' red1 ($⟶ () y')

  deterministic : ∀ {a b c} → (a ⟶ b) → (a ⟶ c) → b ≡ c
  deterministic {C n} () a⟶c
  deterministic {V x} () a⟶c
  deterministic {ƛ x e} () a⟶c
  deterministic {.(ƛ x a) $ .(C n)} (β x a (VC n)) (β .x .a (VC .n)) = refl
  deterministic {.(ƛ x a) $ .(ƛ x' a')} (β x a (Vƛ x' a')) (β .x .a (Vƛ .x' .a'))
    = refl
  deterministic {.(ƛ x a) $ g} (β x a vv) (⟶$ .g ())
  deterministic {.(ƛ x a) $ g} (β x a vv) ($⟶ y y') = ⊥-elim (¬Value⟶ vv y')
  deterministic {.(ƛ x a) $ g} (⟶$ .g ()) (β x a vv)
  deterministic {f $ g} (⟶$ .g y) (⟶$ .g y') rewrite deterministic y y' = refl
  deterministic {f $ g} (⟶$ .g y) ($⟶ y' y0) = ⊥-elim (¬Value⟶ y' y)
  deterministic {.(ƛ x a) $ g} ($⟶ y y') (β x a vv) = ⊥-elim (¬Value⟶ vv y')
  deterministic {f $ g} ($⟶ y y') (⟶$ .g y0) = ⊥-elim (¬Value⟶ y y0)
  deterministic {f $ g} ($⟶ y y') ($⟶ y0 y1) rewrite deterministic y1 y' = refl

  data Terminates (t : Term) : Set where
    done : Value t → Terminates t
    step : ∀ {t'} → (t ⟶ t') → Terminates t' → Terminates t

  -- good luck with that one...
  data Diverges (t : Term) : Set where
    step : ∀ {t'} → (t ⟶ t') → Diverges t' → Diverges t

  data Error (t : Term) : Set where
    stuck : (∀ {t'} → ¬(t ⟶ t')) → ¬(Value t) → Error t
    step : ∀ {t'} → (t ⟶ t') → Error t' → Error t

  terminating : Terminates (
      (ƛ "x" (ƛ "y" (V "y" $ V "x"))) $
      ((ƛ "x" (V "x")) $ C 1) $
      (ƛ "x" (V "x"))
    )
  terminating =
    step (⟶$ (ƛ "x" (V "x")) ($⟶ (Vƛ "x" (ƛ "y" (V "y" $ V "x")))
      (β "x" (V "x") (VC 1)))) (
    step (⟶$ (ƛ "x" (V "x")) (β "x" (ƛ "y" (V "y" $ V "x")) (VC 1))) (
    step (β "y" (V "y" $ C 1) (Vƛ "x" (V "x"))) (
    step (β "x" (V "x") (VC 1)) (
    done (VC 1)))))

  ¬C$C : ∀ {t} → ¬(C 2 $ C 2 ⟶ t)
  ¬C$C (⟶$ .(C 2) ())
  ¬C$C ($⟶ y ())

  error : Error ((ƛ "x" (V "x" $ V "x")) $ C 2)
  error = step
    (β "x" (V "x" $ V "x") (VC 2))
    (stuck stuck1 (λ ()))
    where
      stuck1 : ∀ {t} → ¬(C 2 $ C 2 ⟶ t)
      stuck1 (⟶$ .(C 2) ())
      stuck1 ($⟶ y ())

  {- Not valid:
  diverges : Diverges ((ƛ "x" (V "x" $ V "x")) $ (ƛ "x" (V "x" $ V "x")))
  diverges = step (β "x" (V "x" $ V "x") (Vƛ "x" (V "x" $ V "x"))) diverges
  -}

module CBV-ReductionContext where

  Var : Set
  Var = String

  infixl 2 _$_
  data Term : Set where
    C : (n : ℕ) → Term
    V : (x : Var) → Term
    ƛ : (x : Var) → (e : Term) → Term
    _$_ : (f : Term) → (g : Term) → Term

  data Value : Term → Set where
    VC : ∀ n → Value (C n)
    Vƛ : ∀ x a → Value (ƛ x a)

  _[_←_] : ∀ {v} → Term → Var → Value v → Term
  C n [ x ← v' ] = C n
  V x [ x' ← v' ] with x ≟ x'
  V .x' [ x' ← VC n ] | yes refl = C n
  V .x' [ x' ← Vƛ x a ] | yes refl = ƛ x a
  V x [ x' ← v' ] | no ¬p = V x
  (ƛ x e) [ x' ← v' ] with x ≟ x'
  (ƛ .x' e) [ x' ← v' ] | yes refl = ƛ x' e
  (ƛ x e) [ x' ← v' ] | no ¬p = ƛ x (e [ x' ← v' ])
  (f $ g) [ x ← v' ] = f [ x ← v' ] $ g [ x ← v' ]

  infix 1 _⟶ε_
  data _⟶ε_ : Term → Term → Set where
    β : ∀ {x a v} → (vv : Value v) → (ƛ x a) $ v ⟶ε a [ x ← vv ]

  data Context : Set where
    [] : Context
    <_>_ : (E : Context) → (b : Term) → Context
    _<_> : {v : Term} → (vv : Value v) → (E : Context) → Context

  _[_] : Context → Term → Term
  [] [ a ] = a
  (< E > b) [ a ] =  E [ a ] $ b
  (VC n < E >) [ a ] = C n $ E [ a ]
  (Vƛ x a < E >) [ a' ] = ƛ x a $ E [ a' ]

  infix 1 _⟶_
  data _⟶_ : Term → Term → Set where
    context : ∀ { a a' E } → (a ⟶ε a') → (E [ a ] ⟶ E [ a' ])

  red1 : (ƛ "x" (V "x") $ C 1) ⟶ C 1
  red1 = context {ƛ "x" (V "x") $ C 1} {C 1} {[]} (β (VC 1))

  open import Data.Product using (_×_; _,_)

  ¬Value[ƛ$] : ∀ {E x a t} → ¬ (Value (E [ ƛ x a $ t ]))
  ¬Value[ƛ$] {[]} ()
  ¬Value[ƛ$] {< E > b} ()
  ¬Value[ƛ$] {VC n < E >} ()
  ¬Value[ƛ$] {Vƛ x a < E >} ()

  unique' : ∀ E1 x a g E2 x' a' g' →
    (E1 [ ƛ x a $ g ] ≡ E2 [ ƛ x' a' $ g' ]) → Value g → Value g' →
    (E1 ≡ E2) × ((ƛ x a $ g) ≡ (ƛ x' a' $ g'))
  unique' [] .x' .a' .g' [] x' a' g' refl vg vg' = refl , refl
  unique' [] x a g (< E > b) x' a' g' eq vg vg' = {!!}
  unique' [] x a g (VC n < E >) x' a' g' () vg vg'
  unique' [] .x' .a' .(E [ ƛ x0 a0 $ g' ]) (Vƛ x' a' < E >) x0 a0 g' refl vg vg' = ⊥-elim (¬Value[ƛ$] {E} vg)
  unique' (< E > b) x a g [] x' a' g' eq vg vg' = {!!}
  unique' (< E > b) x a g (< E' > b') x' a' g' eq vg vg' = {!!}
  unique' (< E > b) x a g (VC n < E' >) x' a' g' eq vg vg' = {!!}
  unique' (< E > b) x a g (Vƛ x' a' < E' >) x0 a0 g' eq vg vg' = {!!}
  unique' (VC n < E >) x a g [] x' a' g' () vg vg'
  unique' (Vƛ .x0 .a0 < E >) x' a' g [] x0 a0 .(E [ ƛ x' a' $ g ]) refl vg vg' = {!!}
  unique' (VC n < E >) x a g (< E' > b) x' a' g' eq vg vg' = {!!}
  unique' (Vƛ x a < E >) x' a' g (< E' > b) x0 a0 g' eq vg vg' = {!!}
  unique' (VC n < E >) x a g (VC n' < E' >) x' a' g' eq vg vg' = {!eq!}
  unique' (VC n < E >) x a g (Vƛ x' a' < E' >) x0 a0 g' () vg vg'
  unique' (Vƛ x a < E >) x' a' g (VC n < E' >) x0 a0 g' () vg vg'
  unique' (Vƛ x a < E >) x' a' g (Vƛ x0 a0 < E' >) x1 a1 g' eq vg vg' = {!!}

  unique-decomposition : ∀ a E1 b1 t1 E2 b2 t2 →
    (a ≡ E1 [ b1 ]) → (a ≡ E2 [ b2 ]) →
    (b1 ⟶ε t1) → (b2 ⟶ε t2) →
    (E1 ≡ E2) × (b1 ≡ b2)
  unique-decomposition a E1 (C n) t1 E2 b2 t2 a1 a2 () b2t2
  unique-decomposition a E1 (V x) t1 E2 b2 t2 a1 a2 () b2t2
  unique-decomposition a E1 (ƛ x e) t1 E2 b2 t2 a1 a2 () b2t2
  unique-decomposition a E1 (f $ g) t1 E2 (C n) t2 a1 a2 b1t1 ()
  unique-decomposition a E1 (f $ g) t1 E2 (V x) t2 a1 a2 b1t1 ()
  unique-decomposition a E1 (f $ g) t1 E2 (ƛ x e) t2 a1 a2 b1t1 ()
  unique-decomposition .(E1 [ ƛ x a $ g ]) E1 (.(ƛ x a) $ g) .(a [ x ← vv ]) E2 (.(ƛ x' a') $ g') .(a' [ x' ← vv' ]) refl a2 (β {x} {a} vv) (β {x'} {a'} vv') = {!!}
