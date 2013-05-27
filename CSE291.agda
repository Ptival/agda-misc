module CSE291 where

open import Data.Bool as B using (Bool; true; false; _∧_; _∨_; not)
open import Data.Integer using (ℤ)
  renaming (_+_ to _Z+_; _-_ to _Z-_; _*_ to _Z*_; _≤_ to _Z≤_)
open import Data.Product renaming (Σ to PΣ)
open import Data.String using (String; _≟_)
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

    ECst : ∀ n σ →

      {-------------}
      < AI n , σ >⇓ n

    EVar : ∀ v σ →

      {---------------}
      < AL v , σ >⇓ σ v

    EPlus : ∀ e1 e2 σ n1 n2 →
      < e1 , σ >⇓ n1 →
      < e2 , σ >⇓ n2 →
      {-----------------------}
      < e1 + e2 , σ >⇓ n1 Z+ n2

    EMinus : ∀ e1 e2 σ n1 n2 →
      < e1 , σ >⇓ n1 →
      < e2 , σ >⇓ n2 →
      {-----------------------}
      < e1 - e2 , σ >⇓ n1 Z- n2

    ETimes : ∀ e1 e2 σ n1 n2 →
      < e1 , σ >⇓ n1 →
      < e2 , σ >⇓ n2 →
      {-----------------------}
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

    EEqualsT : ∀ e1 e2 σ n1 n2 →
      EvalAexp.< e1 , σ >⇓ n1 →
      EvalAexp.< e2 , σ >⇓ n2 →
      n1 P≡ n2 →
      {-------------------}
      < e1 ≡ e2 , σ >⇓ true

    EEqualsF : ∀ e1 e2 σ n1 n2 →
      EvalAexp.< e1 , σ >⇓ n1 →
      EvalAexp.< e2 , σ >⇓ n2 →
      ¬ n1 P≡ n2 →
      {--------------------}
      < e1 ≡ e2 , σ >⇓ false

    ELessThanT : ∀ e1 e2 σ n1 n2 →
      EvalAexp.< e1 , σ >⇓ n1 →
      EvalAexp.< e2 , σ >⇓ n2 →
      n1 Z≤ n2 →
      {--------------------}
      < e1 ≤ e2 , σ >⇓ true

    ELessThanF : ∀ e1 e2 σ n1 n2 →
      EvalAexp.< e1 , σ >⇓ n1 →
      EvalAexp.< e2 , σ >⇓ n2 →
      ¬ n1 Z≤ n2 →
      {--------------------}
      < e1 ≤ e2 , σ >⇓ false

    EOr : ∀ e1 e2 σ b1 b2 →
      < e1 , σ >⇓ b1 →
      < e2 , σ >⇓ b2 →
      {----------------------}
      < e1 ∥ e2 , σ >⇓ b1 ∨ b2

    EAnd : ∀ e1 e2 σ b1 b2 →
      < e1 , σ >⇓ b1 →
      < e2 , σ >⇓ b2 →
      {----------------------}
      < e1 & e2 , σ >⇓ b1 ∧ b2

    ENeg : ∀ e σ b →
      < e , σ >⇓ b →
      {----------------}
      < ! e , σ >⇓ not b

_<[_≔_] : Σ → Var → ℤ → Σ
(σ <[ x ≔ n ]) y with x ≟ y
... | yes p = n
... | no  p = σ y

module EvalCmd where

  infix 1 <_,_>⇓_
  data <_,_>⇓_ : Cmd → Σ → Σ → Set where

    Eskip : ∀ σ →

      {-------------}
      < skip , σ >⇓ σ

    ESeq : ∀ c1 c2 σ σ' σ'' →
      < c1 , σ  >⇓ σ'  →
      < c2 , σ' >⇓ σ'' →
      {--------------------}
      < (c1 , c2) , σ >⇓ σ''

    EIfThen : ∀ b c1 c2 σ σ' →
      EvalBexp.< b , σ >⇓ true →
      < c1 , σ >⇓ σ' →
      {--------------------}
      < if b then c1 else c2 , σ >⇓ σ'

    EIfElse : ∀ b c1 c2 σ σ' →
      EvalBexp.< b , σ >⇓ false →
      < c2 , σ >⇓ σ' →
      {--------------------}
      < if b then c1 else c2 , σ >⇓ σ'

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

⊨⟨_⟩_⟨_⟩ : Assn → Cmd → Assn → Set
⊨⟨ A ⟩ c ⟨ B ⟩ = ∀ σ → σ ⊨ A → ∀ σ' → EvalCmd.< c , σ >⇓ σ' → σ' ⊨ B

⊨[_]_[_] : Assn → Cmd → Assn → Set
⊨[ A ] c [ B ] = ∀ σ → σ ⊨ A → ∃ (λ σ' → (EvalCmd.< c , σ >⇓ σ') × (σ' ⊨ B))

data _⇒_ : Assn → Assn → Set where

data ⊢⟨_⟩_⟨_⟩ : Assn → Cmd → Assn → Set where

  ⊢consequence : ∀ A A' B B' c →
    (A' ⇒ A) →
    ⊢⟨ A ⟩ c ⟨ B ⟩ →
    (B' ⇒ B) →
    {--------------}
    ⊢⟨ A' ⟩ c ⟨ B' ⟩

  ⊢skip : ∀ A →

    {---------------}
    ⊢⟨ A ⟩ skip ⟨ A ⟩

  ⊢, : ∀ A B C c1 c2 →
    ⊢⟨ A ⟩ c1 ⟨ B ⟩ →
    ⊢⟨ B ⟩ c1 ⟨ C ⟩ →
    {---------------}
    ⊢⟨ A ⟩ (c1 , c2) ⟨ C ⟩

  ⊢if : ∀ A B b c1 c2 →
    ⊢⟨ A & `B b ⟩   c1 ⟨ B ⟩ →
    ⊢⟨ B & `B (! b) ⟩ c2 ⟨ B ⟩ →
    {-------------------------------}
    ⊢⟨ A ⟩ if b then c1 else c2 ⟨ B ⟩

  ⊢while : ∀ A b c →
    ⊢⟨ A & `B b ⟩ c ⟨ A ⟩ →
    {-------------------------------}
    ⊢⟨ A ⟩ while b do c ⟨ A & `B (! b) ⟩

{- TODO:
  ⊢≔ : ∀ A b c →
-}
