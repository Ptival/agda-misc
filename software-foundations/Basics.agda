module Basics where

open import Relation.Binary.PropositionalEquality

{- Enumerated types -}

{- Days of the week -}

data Day : Set where
  monday    : Day
  tuesday   : Day
  wednesday : Day
  thursday  : Day
  friday    : Day
  saturday  : Day
  sunday    : Day

next-weekday : Day → Day
next-weekday monday    = tuesday
next-weekday tuesday   = wednesday
next-weekday wednesday = thursday
next-weekday thursday  = friday
next-weekday friday    = monday
next-weekday saturday  = monday
next-weekday sunday    = monday

test-next-weekday : (next-weekday (next-weekday saturday)) ≡ tuesday
test-next-weekday = refl

{- Booleans -}

data Bool : Set where
  true  : Bool
  false : Bool

negb : Bool → Bool
negb true  = false
negb false = true

_andb_ : Bool → Bool → Bool
true andb b  = b
false andb _ = false

_orb_ : Bool → Bool → Bool
true orb _  = true
false orb b = b

test-orb-1 : true orb false ≡ true
test-orb-1 = refl

test-orb-2 : false orb false ≡ false
test-orb-2 = refl

test-orb-3 : false orb true ≡ true
test-orb-3 = refl

test-orb-4 : true orb true ≡ true
test-orb-4 = refl

nandb : Bool → Bool → Bool
nandb true true = false
nandb _    _    = true

test-nandb-1 : nandb true false ≡ true
test-nandb-1 = refl

test-nandb-2 : nandb false false ≡ true
test-nandb-2 = refl

test-nandb-3 : nandb false true ≡ true
test-nandb-3 = refl

test-nandb-4 : nandb true true ≡ false
test-nandb-4 = refl

andb3 : Bool → Bool → Bool → Bool
andb3 true true true = true
andb3 _    _    _    = false

test-andb3-1 : andb3 true true true ≡ true
test-andb3-1 = refl

test-andb3-2 : andb3 false true true ≡ false
test-andb3-2 = refl

test-andb3-3 : andb3 true false true ≡ false
test-andb3-3 = refl

test-andb3-4 : andb3 true true false ≡ false
test-andb3-4 = refl

{- Numbers -}

data ℕ : Set where
  O : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO O #-}
{-# BUILTIN SUC S #-}

pred : ℕ → ℕ
pred O = O
pred (S n) = n

-2 : ℕ → ℕ
-2 O = O
-2 (S O) = O
-2 (S (S n)) = n

even? : ℕ → Bool
even? O = true
even? (S O) = false
even? (S (S n)) = even? n

infixl 6 _+_ _∸_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
O + b = b
S n + b = S (n + b)

_*_ : ℕ → ℕ → ℕ
O * _ = O
S n * n' = n' + (n * n')

_∸_ : ℕ → ℕ → ℕ
O ∸ _ = O
n ∸ O = n
S n ∸ S n' = n ∸ n'

exp : ℕ → ℕ → ℕ
exp base O = S O
exp base (S n) = base * (exp base n)

test-mult-1 :  3 * 3 ≡ 9
test-mult-1 = refl

infix 8 _!

_! : ℕ → ℕ
O ! = 1
(S n) ! = (S n) * n !

test-!-1 : 3 ! ≡ 6
test-!-1 = refl

test-!-2 : 5 ! ≡ 10 * 12
test-!-2 = refl

infix 5 _≡ℕ?_ _≤ℕ?_ _<ℕ?_

_≡ℕ?_ : ℕ → ℕ → Bool
O ≡ℕ? O = true
O ≡ℕ? (S n) = false
S n ≡ℕ? O = false
S n ≡ℕ? S n' = n ≡ℕ? n'

_≤ℕ?_ : ℕ → ℕ → Bool
O ≤ℕ? _ = true
S n ≤ℕ? O = false
S n ≤ℕ? S n' = n ≤ℕ? n'

test-≤ℕ?-1 : 2 ≤ℕ? 2 ≡ true
test-≤ℕ?-1 = refl

test-≤ℕ?-2 : 2 ≤ℕ? 4 ≡ true
test-≤ℕ?-2 = refl

test-≤ℕ?-3 : 4 ≤ℕ? 2 ≡ false
test-≤ℕ?-3 = refl

_<ℕ?_ : ℕ → ℕ → Bool
O <ℕ? O = false
O <ℕ? S n = true
S n <ℕ? O = false
S n <ℕ? S n' = n <ℕ? n'

test-<ℕ-1 : 2 <ℕ? 2 ≡ false
test-<ℕ-1 = refl

test-<ℕ-2 : 2 <ℕ? 4 ≡ true
test-<ℕ-2 = refl

test-<ℕ-3 : 4 <ℕ? 2 ≡ false
test-<ℕ-3 = refl

{- Proof by simplification -}

0+n : ∀ {n} → 0 + n ≡ n
0+n = refl

{- The intros tactic -}

1+n : ∀ {n} → 1 + n ≡ S n
1+n = refl

0*n : ∀ {n} → 0 * n ≡ 0
0*n = refl

{- Proof by rewriting -}

+id : ∀ {n m} → n ≡ m → n + n ≡ m + m
+id refl = refl

0+* : ∀ {n m} → (0 + n) * m ≡ n * m
0+* = refl

1+* : ∀ {n m} → (1 + n) * m ≡ m + (n * m)
1+* = refl

{- Case analysis -}

+1≢ℕ0 : ∀ {n} → n + 1 ≡ℕ? 0 ≡ false
+1≢ℕ0 {O} = refl
+1≢ℕ0 {S n} = refl

negb-involutive : ∀ {b} → negb (negb b) ≡ b
negb-involutive {true} = refl
negb-involutive {false} = refl

0≢ℕ+1 : ∀ {n} → 0 ≡ℕ? n + 1 ≡ false
0≢ℕ+1 {O} = refl
0≢ℕ+1 {S n} = refl

{- Naming cases -}

andb-true-elim-1 : ∀ {b c} → b andb c ≡ true → b ≡ true
andb-true-elim-1 {true} _ = refl
andb-true-elim-1 {false} {true} ()
andb-true-elim-1 {false} {false} ()

andb-true-elim-2 : ∀ {b c} → b andb c ≡ true → c ≡ true
andb-true-elim-2 {_} {true} _ = refl
andb-true-elim-2 {true} {false} ()
andb-true-elim-2 {false} {false} ()

{- Induction -}

{- with "with" -}
+0 : ∀ {n} → n + 0 ≡ n
+0 {O} = refl
+0 {S n} with n + 0 | +0 {n}
+0 {S n} | .n | refl = refl

{- with "cong" -}
open import Relation.Binary.PropositionalEquality
+0' : ∀ {n} → n + 0 ≡ n
+0' {O} = refl
+0' {S n} with +0 {n}
+0' {S n} | +0n = cong S +0n

∸-diag : ∀ {n} → n ∸ n ≡ 0
∸-diag {O} = refl
∸-diag {S n} = ∸-diag {n}

*0 : ∀ {n} → n * 0 ≡ 0
*0 {O} = refl
*0 {S n} = *0 {n}

n+Sm : ∀ {n m} → S (n + m) ≡ n + S m
n+Sm {O} = refl
n+Sm {S n} {m} = cong S (n+Sm {n} {m})

+-comm : ∀ {n m} → n + m ≡ m + n
+-comm {O} = sym +0
+-comm {S n} {m} rewrite sym (n+Sm {m} {n}) = cong S (+-comm {n} {m})

double : ℕ → ℕ
double O = O
double (S n) = S (S (double n))

double+ : ∀ {n} → double n ≡ n + n
double+ {O} = refl
double+ {S n} rewrite double+ {n} = cong S (n+Sm {n} {n})

{- Formal vs. informal proof -}

+-assoc : ∀ {n m p} → n + (m + p) ≡ (n + m) + p
+-assoc {O} = refl
+-assoc {S n} {m} {p} rewrite +-assoc {n} {m} {p} = refl

≡ℕ?-refl : ∀ {n} → true ≡ n ≡ℕ? n
≡ℕ?-refl {O} = refl
≡ℕ?-refl {S n} = ≡ℕ?-refl {n}

{- Proofs within proofs -}

+-rearrange : ∀ {n m p q} → (n + m) + (p + q) ≡ (m + n) + (p + q)
+-rearrange {n} {m} {p} {q} rewrite +-comm {n} {m} | +-comm {p} {q} = refl

+-swap : ∀ {n m p} → n + (m + p) ≡ m + (n + p)
+-swap {n} {m} {p} rewrite +-assoc {n} {m} {p}
                         | +-comm {n} {m}
                         | +-assoc {m} {n} {p}
                         = refl

*-comm : ∀ {n m} → n * m ≡ m * n
*-comm {O} {m} = sym (*0 {m})
*-comm {n} {O} = *0 {n}
*-comm {S n} {S m} rewrite *-comm {n} {S m}
                         | sym (*-comm {S n} {m})
                         | *-comm {n} {m}
                         = cong S (+-swap {m} {n} {m * n})

even?-n-odd?-S-n : ∀ {n} → even? n ≡ negb (even? (S n))
even?-n-odd?-S-n {O} = refl
even?-n-odd?-S-n {S n} rewrite even?-n-odd?-S-n {n} =
  sym (negb-involutive {even? (S n)})

{- More exercises -}

≤ℕ?-refl : ∀ {n} → true ≡ n ≤ℕ? n
≤ℕ?-refl {O} = refl
≤ℕ?-refl {S n} = ≤ℕ?-refl {n}

O≢ℕS : ∀ {n} → 0 ≡ℕ? S n ≡ false
O≢ℕS = refl

andb-false-r : ∀ {b} → b andb false ≡ false
andb-false-r {true} = refl
andb-false-r {false} = refl

+-≤ℕ?-compat : ∀ {n m p} → n ≤ℕ? m ≡ true → p + n ≤ℕ? p + m ≡ true
+-≤ℕ?-compat {n} {m} {O} n≤m = n≤m
+-≤ℕ?-compat {n} {m} {S n'} n≤m = +-≤ℕ?-compat {n} {m} {n'} n≤m

S≢ℕO : ∀ {n} → S n ≡ℕ? O ≡ false
S≢ℕO = refl

1* : ∀ n → 1 * n ≡ n
1* n = +0 {n}

all3-spec : ∀ {b c} → (b andb c) orb ((negb b) orb (negb c)) ≡ true
all3-spec {true} {true} = refl
all3-spec {true} {false} = refl
all3-spec {false} = refl

*-+-distr-r : ∀ {n m p} → (n + m) * p ≡ (n * p) + (m * p)
*-+-distr-r {n} {m} {O}
  rewrite *0 {n + m}
  | *0 {n}
  | *0 {m}
  = refl
*-+-distr-r {n} {m} {S p}
  rewrite *-comm {n + m} {S p}
  | *-comm {n} {S p}
  | *-comm {m} {S p}
  | *-comm {p} {n + m}
  | *-+-distr-r {n} {m} {p}
  | *-comm {n} {p}
  | *-comm {m} {p}
  | sym (+-assoc {n} {m} {p * n + p * m})
  | +-swap {m} {p * n} {p * m}
  | +-assoc {n} {p * n} {m + p * m}
  = refl

open ≡-Reasoning

*-+-distr-r' : ∀ {n m p} → (n + m) * p ≡ (n * p) + (m * p)
*-+-distr-r' {n} {m} {O} = begin
  (n + m) * 0   ≡⟨ *0 {n + m} ⟩
  0             ≡⟨ refl ⟩ -- optional
  0 + 0         ≡⟨ sym (cong₂ _+_ (*0 {n}) (*0 {m})) ⟩
  n * 0 + m * 0 ∎
*-+-distr-r' {n} {m} {S p} = begin
  (n + m) * S p         ≡⟨ *-comm {n + m} {S p} ⟩
  S p * (n + m)         ≡⟨ refl ⟩ -- optional
  (n + m) + p * (n + m) ≡⟨ cong (λ x → n + m + x) (*-comm {p} {n + m}) ⟩
  (n + m) + (n + m) * p ≡⟨ cong (λ x → n + m + x) (*-+-distr-r' {n} {m} {p}) ⟩
  (n + m) + (n * p + m * p) ≡⟨ sym (+-assoc {n} {m} {n * p + m * p}) ⟩
  n + (m + (n * p + m * p)) ≡⟨ cong (λ x -> n + x) (+-swap {m} {n * p} {m * p}) ⟩
  n + (n * p + (m + m * p)) ≡⟨ +-assoc {n} {n * p} {m + m * p} ⟩
  (n + n * p) + (m + m * p)
  ≡⟨ cong (λ x → (n + x) + (m + m * p)) (*-comm {n} {p}) ⟩
  (n + p * n) + (m + m * p)
  ≡⟨ cong (λ x → (n + p * n) + (m + x)) (*-comm {m} {p}) ⟩
  (n + p * n) + (m + p * m) ≡⟨ refl ⟩
  S p * n + S p * m ≡⟨ cong (λ x -> x + S p * m) (*-comm {S p} {n}) ⟩
  n * S p + S p * m ≡⟨ cong (λ x -> n * S p + x) (*-comm {S p} {m}) ⟩
  n * S p + m * S p ∎

*-assoc : ∀ {n m p} → n * (m * p) ≡ (n * m) * p
*-assoc {n} {O} rewrite *0 {n} = refl
*-assoc {n} {S m} {p}
  rewrite *-comm {n} {S m}
  | *-+-distr-r {n} {m * n} {p}
  | *-comm {n} {p + m * p}
  | *-+-distr-r {p} {m * p} {n}
  | sym (*-assoc {m} {p} {n})
  | *-comm {p} {n}
  | *-assoc {m} {n} {p}
  = refl

data Bin : Set where
  O     : Bin
  2*_   : Bin → Bin
  2*_+1 : Bin → Bin

incr : Bin → Bin
incr O = 2* O +1
incr (2* y) = 2* y +1
incr 2* y +1 = 2* (incr y)

Bin→ℕ : Bin → ℕ
Bin→ℕ O = 0
Bin→ℕ (2* y) = (Bin→ℕ y) * 2
Bin→ℕ 2* y +1 =  (Bin→ℕ y) * 2 + 1

incr-conv-comm : ∀ {n} → Bin→ℕ (incr n) ≡ (Bin→ℕ n) + 1
incr-conv-comm {O} = refl
incr-conv-comm {2* y} = refl
incr-conv-comm {2* y +1}
  rewrite incr-conv-comm {y}
  | *-+-distr-r {Bin→ℕ y} {1} {2}
  | sym (+-assoc {Bin→ℕ y * 2} {1} {1})
  = refl

data Parity : ℕ → Set where
  even : ∀ {n} → Parity (n * 2)
  odd  : ∀ {n} → Parity (1 + n * 2)

parity : (n : ℕ) → Parity n
parity O = even {0}
parity (S n) with parity n
parity (S .(n * 2)) | even {n} = odd {n}
parity (S .(S (n * 2))) | odd {n} = even {S n}
