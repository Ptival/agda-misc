module CSE291 where

open import Data.Bool as B using (Bool; true; false; _∧_; _∨_; not)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _Z+_; _-_ to _Z-_; _*_ to _Z*_; _≤_ to _Z≤_)
open import Data.Product renaming (Σ to PΣ)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (Unit; unit)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _P≡_)

Var : Set
Var = String

data Aexp : Set where
  AI : ℤ → Aexp
  AL : Var → Aexp
  _+_ : Aexp → Aexp → Aexp
  _-_ : Aexp → Aexp → Aexp
  _*_ : Aexp → Aexp → Aexp

data Bexp : Set where
  true : Bexp
  false : Bexp
  _≡_ : Aexp → Aexp → Bexp
  _≤_ : Aexp → Aexp → Bexp
  !_ : Bexp → Bexp
  _∥_ : Bexp → Bexp → Bexp
  _&_ : Bexp → Bexp → Bexp

data Cmd : Set where
  skip : Cmd
  _≔_ : Var → Aexp → Cmd
  _,_ : Cmd → Cmd → Cmd
  if_then_else_ : Bexp → Cmd → Cmd → Cmd
  while_do_ : Bexp → Cmd → Cmd

Σ : Set
Σ = Var → ℤ

module EvalAexp where

  infix 1 <_,_>⇓_
  data <_,_>⇓_ : Aexp → Σ → ℤ → Set where

    ECst : ∀ {n σ} →


      {-------------}
      < AI n , σ >⇓ n

    EVar : ∀ {v σ} →


      {---------------}
      < AL v , σ >⇓ σ v

    EPlus : ∀ {e1 e2 σ n1 n2} →

      < e1 , σ >⇓ n1   →   < e2 , σ >⇓ n2   →
      {-------------------------------------}
      < e1 + e2 , σ >⇓ n1 Z+ n2

    EMinus : ∀ {e1 e2 σ n1 n2} →

      < e1 , σ >⇓ n1   →   < e2 , σ >⇓ n2   →
      {-------------------------------------}
      < e1 - e2 , σ >⇓ n1 Z- n2

    ETimes : ∀ {e1 e2 σ n1 n2} →

      < e1 , σ >⇓ n1   →   < e2 , σ >⇓ n2   →
      {-------------------------------------}
      < e1 * e2 , σ >⇓ n1 Z* n2

module EvalBexp where

  infix 1 <_,_>⇓_
  data <_,_>⇓_ : Bexp → Σ → Bool → Set where

    ETrue : ∀ σ →


      {----------------}
      < true , σ >⇓ true

    EFalse : ∀ σ →


      {------------------}
      < false , σ >⇓ false

    EEqualsT : ∀ {e1 e2 σ n1 n2} →

      EvalAexp.< e1 , σ >⇓ n1   →   EvalAexp.< e2 , σ >⇓ n2   →   n1 P≡ n2   →
      {----------------------------------------------------------------------}
      < e1 ≡ e2 , σ >⇓ true

    EEqualsF : ∀ {e1 e2 σ n1 n2} →

      EvalAexp.< e1 , σ >⇓ n1   →   EvalAexp.< e2 , σ >⇓ n2   →   ¬ n1 P≡ n2   →
      {------------------------------------------------------------------------}
      < e1 ≡ e2 , σ >⇓ false

    ELessThanT : ∀ {e1 e2 σ n1 n2} →

      EvalAexp.< e1 , σ >⇓ n1   →   EvalAexp.< e2 , σ >⇓ n2   →   n1 Z≤ n2 →
      {--------------------------------------------------------------------}
      < e1 ≤ e2 , σ >⇓ true

    ELessThanF : ∀ {e1 e2 σ n1 n2} →

      EvalAexp.< e1 , σ >⇓ n1   →   EvalAexp.< e2 , σ >⇓ n2   →   ¬ n1 Z≤ n2   →
      {------------------------------------------------------------------------}
      < e1 ≤ e2 , σ >⇓ false

    EOr : ∀ {e1 e2 σ b1 b2} →

      < e1 , σ >⇓ b1   →   < e2 , σ >⇓ b2   →
      {-------------------------------------}
      < e1 ∥ e2 , σ >⇓ b1 ∨ b2

    EAnd : ∀ {e1 e2 σ b1 b2} →

      < e1 , σ >⇓ b1   →   < e2 , σ >⇓ b2   →
      {-------------------------------------}
      < e1 & e2 , σ >⇓ b1 ∧ b2

    ENeg : ∀ {e σ b} →

      < e , σ >⇓ b   →
      {----------------}
      < ! e , σ >⇓ not b

_<[_≔_] : Σ → Var → ℤ → Σ
(σ <[ x ≔ n ]) y with x ≟ y
... | yes _ = n
... | no  _ = σ y

module EvalCmd where

  infix 1 <_,_>⇓_
  data <_,_>⇓_ : Cmd → Σ → Σ → Set where

    Eskip : ∀ {σ} →


      {-------------}
      < skip , σ >⇓ σ

    Eseq : ∀ {c1 c2 σ σ''} σ' →

      < c1 , σ  >⇓ σ'   →   < c2 , σ' >⇓ σ''   →
      {----------------------------------------}
      < (c1 , c2) , σ >⇓ σ''

    E≔ : ∀ {x e σ n} →

      EvalAexp.< e , σ  >⇓ n   →
      {------------------------}
      < x ≔ e , σ >⇓ σ <[ x ≔ n ]

    EIfThen : ∀ {b c1 c2 σ σ'} →

      EvalBexp.< b , σ >⇓ true   →   < c1 , σ >⇓ σ'   →
      {-----------------------------------------------}
      < if b then c1 else c2 , σ >⇓ σ'

    EIfElse : ∀ {b c1 c2 σ σ'} →

      EvalBexp.< b , σ >⇓ false   →   < c2 , σ >⇓ σ'   →
      {------------------------------------------------}
      < if b then c1 else c2 , σ >⇓ σ'

    EWhileFalse : ∀ {b c σ} →

      EvalBexp.< b , σ >⇓ false   →
      {---------------------------}
      < while b do c , σ >⇓ σ

    EWhileTrue : ∀ {b c σ σ' σ''} →

      EvalBexp.< b , σ >⇓ true   →   < c , σ >⇓ σ'   →   < while b do c , σ' >⇓ σ''   →
      {-------------------------------------------------------------------------------}
      < while b do c , σ >⇓ σ''

data Assn : Set where
  true : Assn
  `B : Bexp → Assn
  _≡_ : Aexp → Aexp → Assn
  _≤_ : Aexp → Aexp → Assn
  _&_ : Assn → Assn → Assn
  _∥_ : Assn → Assn → Assn
  _`⇒_ : Assn → Assn → Assn
  `∃_,_ : Var → Assn → Assn
  `∀_,_ : Var → Assn → Assn

{-
infix 0 _⊨_
data _⊨_ : Σ → Assn → Set where

  ⊨true : ∀ σ →

    {------}
    σ ⊨ true

  ⊨≡ : ∀ e1 e2 σ n1 n2 →
    EvalAexp.< e1 , σ >⇓ n1 →
    EvalAexp.< e2 , σ >⇓ n2 →
    n1 P≡ n2 →
    {-----------------------}
    σ ⊨ e1 ≡ e2

  ⊨≤ : ∀ e1 e2 σ n1 n2 →
    EvalAexp.< e1 , σ >⇓ n1 →
    EvalAexp.< e2 , σ >⇓ n2 →
    n1 Z≤ n2 →
    {-----------------------}
    σ ⊨ e1 ≤ e2

  ⊨& : ∀ a1 a2 σ →
    σ ⊨ a1 →
    σ ⊨ a2 →
    {---------}
    σ ⊨ a1 & a2

  ⊨∥1 : ∀ a1 a2 σ →
    σ ⊨ a1 →
    {---------}
    σ ⊨ a1 ∥ a2

  ⊨∥2 : ∀ a1 a2 σ →
    σ ⊨ a2 →
    {---------}
    σ ⊨ a1 ∥ a2

{- Negative occurence :(
  ⊨⇒ : ∀ a1 a2 σ →
    (σ ⊨ a1 → σ ⊨ a2) →
    {-----------------}
    σ ⊨ a1 ⇒ a2
-}

  ⊨∃ : ∀ x a σ →
    ∃ (λ n → σ <[ x ≔ n ] ⊨ a) →
    {----------------}
    σ ⊨ `∃ x , a

  ⊨∀ : ∀ x a σ →
    (∀ n → σ <[ x ≔ n ] ⊨ a) →
    {----------------}
    σ ⊨ `∀ x , a
-}

infix 5 _⊨_
_⊨_ : Σ → Assn → Set
σ ⊨ true     = Unit
σ ⊨ `B x     = EvalBexp.< x , σ >⇓ true
σ ⊨ a ≡ b    = ∃ (λ n1 → ∃ (λ n2 → (EvalAexp.< a , σ >⇓ n1) × (EvalAexp.< b , σ >⇓ n2) × (n1 P≡ n2)))
σ ⊨ a ≤ b    = ∃ (λ n1 → ∃ (λ n2 → (EvalAexp.< a , σ >⇓ n1) × (EvalAexp.< b , σ >⇓ n2) × (n1 Z≤ n2)))
σ ⊨ a & b    = σ ⊨ a × σ ⊨ b
σ ⊨ a ∥ b    = σ ⊨ a ⊎ σ ⊨ b
σ ⊨ a `⇒ b   = σ ⊨ a → σ ⊨ b
σ ⊨ `∃ x , a = ∃ (λ n → σ <[ x ≔ n ] ⊨ a)
σ ⊨ `∀ x , a = ∀ n → σ <[ x ≔ n ] ⊨ a

⊨⟨_⟩_⟨_⟩ : Assn → Cmd → Assn → Set
⊨⟨ A ⟩ c ⟨ B ⟩ = ∀ {σ} → σ ⊨ A → ∀ {σ'} → EvalCmd.< c , σ >⇓ σ' → σ' ⊨ B

⊨[_]_[_] : Assn → Cmd → Assn → Set
⊨[ A ] c [ B ] = ∀ σ → σ ⊨ A → ∃ (λ σ' → (EvalCmd.< c , σ >⇓ σ') × (σ' ⊨ B))

module SubstAexp where

  _[_/_] : Aexp → Aexp → Var → Aexp
  AI n    [ e / x ] = AI n
  AL v    [ e / x ] with v ≟ x
  ... | yes _ = e
  ... | no  _ = AL v
  (a + b) [ e / x ] = (a [ e / x ]) + (b [ e / x ])
  (a - b) [ e / x ] = (a [ e / x ]) - (b [ e / x ])
  (a * b) [ e / x ] = (a [ e / x ]) * (b [ e / x ])

module SubstBexp where

  _[_/_] : Bexp → Aexp → Var → Bexp
  true    [ e / x ] = true
  false   [ e / x ] = false
  (a ≡ b) [ e / x ] = a SubstAexp.[ e / x ] ≡ b SubstAexp.[ e / x ]
  (a ≤ b) [ e / x ] = a SubstAexp.[ e / x ] ≤ b SubstAexp.[ e / x ]
  (! b)   [ e / x ] = ! (b [ e / x ])
  (a ∥ b) [ e / x ] = a [ e / x ] ∥ b [ e / x ]
  (a & b) [ e / x ] = a [ e / x ] & b [ e / x ]

module SubstAssn where

  _[_/_] : Assn → Aexp → Var → Assn
  true       [ e / x ] = true
  `B b       [ e / x ] = `B (b SubstBexp.[ e / x ])
  (a ≡ b)    [ e / x ] = (a SubstAexp.[ e / x ]) ≡ (b SubstAexp.[ e / x ])
  (a ≤ b)    [ e / x ] = (a SubstAexp.[ e / x ]) ≤ (b SubstAexp.[ e / x ])
  (A & B)    [ e / x ] = (A [ e / x ]) & (B [ e / x ])
  (A ∥ B)    [ e / x ] = (A [ e / x ]) ∥ (B [ e / x ])
  (A `⇒ B)   [ e / x ] = (A [ e / x ]) `⇒ (B [ e / x ])
  (`∃ y , A) [ e / x ] with y ≟ x
  ... | yes _ = `∃ y , A
  ... | no  _ = `∃ y , A [ e / x ]
  (`∀ y , A) [ e / x ] with y ≟ x
  ... | yes _ = `∀ y , A
  ... | no  _ = `∀ y , A [ e / x ]

_⇒_ : Assn → Assn → Set
A ⇒ B = ∀ {σ} → σ ⊨ A → σ ⊨ B

data ⊢⟨_⟩_⟨_⟩ : Assn → Cmd → Assn → Set where

  ⊢consequence : ∀ {A' B' c} A B →

    (A' ⇒ A)   →   ⊢⟨ A ⟩ c ⟨ B ⟩   →   (B ⇒ B')   →
    {----------------------------------------------}
    ⊢⟨ A' ⟩ c ⟨ B' ⟩

  ⊢skip : ∀ {A} →


    {---------------}
    ⊢⟨ A ⟩ skip ⟨ A ⟩

  ⊢, : ∀ {A B C c1 c2} →

    ⊢⟨ A ⟩ c1 ⟨ B ⟩   →   ⊢⟨ B ⟩ c2 ⟨ C ⟩   →
    {---------------------------------------}
    ⊢⟨ A ⟩ (c1 , c2) ⟨ C ⟩

  ⊢if : ∀ {A B b c1 c2} →

    ⊢⟨ A & `B b ⟩   c1 ⟨ B ⟩   →   ⊢⟨ A & `B (! b) ⟩ c2 ⟨ B ⟩   →
    {-----------------------------------------------------------}
    ⊢⟨ A ⟩ if b then c1 else c2 ⟨ B ⟩

  ⊢while : ∀ {A b c} →

    ⊢⟨ A & `B b ⟩ c ⟨ A ⟩ →
    {-------------------------------}
    ⊢⟨ A ⟩ while b do c ⟨ A & `B (! b) ⟩

  ⊢≔ : ∀ {A e x} →


    {------------------------------------}
    ⊢⟨ A SubstAssn.[ e / x ] ⟩ x ≔ e ⟨ A ⟩

module ExampleConditional where

  x : Aexp
  x = AL "x"

  y : Aexp
  y = AL "y"

  `0 : Aexp
  `0 = AI (+ 0)

  `1 : Aexp
  `1 = AI (+ 1)

  ¬1≤0 : (+ 1) Z≤ (+ 0) → ⊥
  ¬1≤0 (Data.Integer.+≤+ ())

  example01 : ⊢⟨ true ⟩ if y ≤ `0 then "x" ≔ `1 else ("x" ≔ y) ⟨ `B (! (x ≤ `0)) ⟩
  example01 = ⊢if {!!} {!!}

soundness : ∀ {A c B} → ⊢⟨ A ⟩ c ⟨ B ⟩ → ⊨⟨ A ⟩ c ⟨ B ⟩
soundness (⊢consequence A B A'⇒A ⊢AcB B⇒B') σ⊨A' Ec = B⇒B' (soundness ⊢AcB (A'⇒A σ⊨A') Ec)
soundness ⊢skip σ⊨A EvalCmd.Eskip = σ⊨A
soundness (⊢, ⊢Ac₁X ⊢Xc₂B) σ⊨A (EvalCmd.Eseq σX Ec₁ Ec₂) =
  let ⊨Ac₁X = soundness ⊢Ac₁X in
  let ⊨Xc₂B = soundness ⊢Xc₂B in
  let σX⊨X = ⊨Ac₁X σ⊨A Ec₁ in
  let σ'⊨B = ⊨Xc₂B σX⊨X Ec₂ in
  σ'⊨B
soundness (⊢if ⊢AcT ⊢AcE) σ⊨A (EvalCmd.EIfThen x Ec) = soundness ⊢AcT (σ⊨A , x) Ec
soundness (⊢if ⊢AcT ⊢AcE) σ⊨A (EvalCmd.EIfElse x Ec) = soundness ⊢AcE (σ⊨A , EvalBexp.ENeg x) Ec
soundness (⊢while ⊢AcB) σ⊨A (EvalCmd.EWhileFalse x) = σ⊨A , EvalBexp.ENeg x
soundness (⊢while ⊢AcB) σ⊨A (EvalCmd.EWhileTrue x Ec Ewhile) =
  let σ''⊨A = soundness ⊢AcB (σ⊨A , x) Ec in
  soundness (⊢while ⊢AcB) σ''⊨A Ewhile
soundness ⊢≔ σ⊨A Ec = {!!} -- left as an exercise for the reader
