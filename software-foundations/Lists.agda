module Lists where

open import Basics
open import Relation.Binary.PropositionalEquality

module [ℕ] where

  data ℕ×ℕ : Set where
    _,_ : (a : ℕ) → (b : ℕ) → ℕ×ℕ

  fst : ℕ×ℕ → ℕ
  fst (a , _) = a

  snd : ℕ×ℕ → ℕ
  snd (_ , b) = b

  swap-pair : ℕ×ℕ → ℕ×ℕ
  swap-pair (a , b) = (b , a)

  surjective-pairing : ∀ {n m} → (n , m) ≡ (fst (n , m) , snd (n , m))
  surjective-pairing = refl

  surjective-pairing-stuck : ∀ {p} → p ≡ (fst p , snd p)
  surjective-pairing-stuck {a , b} = refl

  snd-fst≡swap : ∀ {p} → (snd p , fst p) ≡ swap-pair p
  snd-fst≡swap {a , b} = refl

  fst-swap≡snd : ∀ {p} → fst (swap-pair p) ≡ snd p
  fst-swap≡snd {a , b} = refl

  infixr 8 _∷_
  data [ℕ] : Set where
    [] : [ℕ]
    _∷_ : (x : ℕ) → (xs : [ℕ]) → [ℕ]

  repeat : ℕ → ℕ → [ℕ]
  repeat _ 0 = []
  repeat x (S n) = x ∷ (repeat x n)

  length : [ℕ] → ℕ
  length [] = 0
  length (_ ∷ t) = 1 + length t

  _++_ : [ℕ] → [ℕ] → [ℕ]
  [] ++ l = l
  (a ∷ tl) ++ l = a ∷ (tl ++ l)

  head : ℕ → [ℕ] → ℕ
  head d [] = d
  head _ (n ∷ _) = n

  tail : [ℕ] → [ℕ]
  tail [] = []
  tail (_ ∷ tl) = tl

  non-zeros : [ℕ] → [ℕ]
  non-zeros [] = []
  non-zeros (0 ∷ tl) = non-zeros tl
  non-zeros (x ∷ tl) = x ∷ non-zeros tl

  test-non-zeros : non-zeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  test-non-zeros = refl

  odd-members : [ℕ] → [ℕ]
  odd-members [] = []
  odd-members (hd ∷ tl) with parity hd
  odd-members (.(n * 2) ∷ tl) | even {n} = odd-members tl
  odd-members (.(S (n * 2)) ∷ tl) | odd {n} = (S (n * 2)) ∷ odd-members tl

  test-odd-members : odd-members (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ (1 ∷ 3 ∷ [])
  test-odd-members = refl

  count-odd-members : [ℕ] → ℕ
  count-odd-members [] = 0
  count-odd-members (hd ∷ tl) with parity hd
  count-odd-members (.(n * 2) ∷ tl) | even {n} = count-odd-members tl
  count-odd-members (.(S (n * 2)) ∷ tl) | odd {n} = 1 + count-odd-members tl

  test-count-odd-members-1 : count-odd-members (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
  test-count-odd-members-1 = refl

  test-count-odd-members-2 : count-odd-members (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
  test-count-odd-members-2 = refl

  test-count-odd-members-3 : count-odd-members [] ≡ 0
  test-count-odd-members-3 = refl

  alternate : [ℕ] → [ℕ] → [ℕ]
  alternate [] l = l
  alternate (x ∷ xs) ys = x ∷ alternate ys xs

  test-alternate-1 :
    alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ 6 ∷ [])
  test-alternate-1 = refl

  test-alternate-2 : alternate (1 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ (1 ∷ 4 ∷ 5 ∷ 6 ∷ [])
  test-alternate-2 = refl

  test-alternate-3 : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ []) ≡ (1 ∷ 4 ∷ 2 ∷ 3 ∷ [])
  test-alternate-3 = refl

  test-alternate-4 : alternate [] (20 ∷ 30 ∷ []) ≡ (20 ∷ 30 ∷ [])
  test-alternate-4 = refl

  bag : Set
  bag = [ℕ]

  data Eq?ℕ (a : ℕ) : ℕ → Set where
    eq : Eq?ℕ a a
    neq : ∀ {b} → a ≢ b → Eq?ℕ a b

  -1≡-1 : ∀ {n m} → S n ≡ S m → n ≡ m
  -1≡-1 {O} {O} _ = refl
  -1≡-1 {O} {S m} ()
  -1≡-1 {S n} {O} ()
  -1≡-1 {S .m} {S m} refl = refl

  eq?ℕ : (n m : ℕ) → Eq?ℕ n m
  eq?ℕ O O = eq
  eq?ℕ O (S n) = neq (λ ())
  eq?ℕ (S n) O = neq (λ ())
  eq?ℕ (S n) (S m) with eq?ℕ n m
  eq?ℕ (S n) (S .n) | eq = eq
  eq?ℕ (S n) (S m) | neq n≢m = neq (λ Sn≡Sm -> n≢m (-1≡-1 Sn≡Sm))

  count : ℕ → bag → ℕ
  count v [] = 0
  count v (y ∷ ys) with eq?ℕ v y
  count v (.v ∷ ys) | eq = 1 + count v ys
  count v (y ∷ ys) | neq y' = count v ys

  test-count-1 : count 1 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 3
  test-count-1 = refl

  test-count-2 : count 6 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 0
  test-count-2 = refl

  sum : bag → bag → bag
  sum = _++_

  test-sum-1 : count 1 (sum (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
  test-sum-1 = refl

  add : ℕ → bag → bag
  add = _∷_

  test-add-1 : count 1 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
  test-add-1 = refl

  test-add-2 : count 5 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-add-2 = refl

  member : ℕ → bag → Bool
  member _ [] = false
  member n (x ∷ xs) with eq?ℕ n x
  member .x (x ∷ xs) | eq = true
  member n (x ∷ xs) | neq _ = member n xs

  test-member-1 : member 1 (1 ∷ 4 ∷ 1 ∷ []) ≡ true
  test-member-1 = refl

  test-member-2 : member 2 (1 ∷ 4 ∷ 1 ∷ []) ≡ false
  test-member-2 = refl

  remove-one : ℕ → bag → bag
  remove-one n [] = []
  remove-one n (x ∷ xs) with eq?ℕ n x
  remove-one .x (x ∷ xs) | eq = xs
  remove-one n (x ∷ xs) | neq y = x ∷ remove-one n xs

  test-remove-one-1 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-one-1 = refl

  test-remove-one-2 : count 5 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-one-2 = refl

  test-remove-one-3 : count 4 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 2
  test-remove-one-3 = refl

  test-remove-one-4 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 1
  test-remove-one-4 = refl

  remove-all : ℕ → bag → bag
  remove-all _ [] = []
  remove-all n (x ∷ xs) with eq?ℕ n x
  remove-all .x (x ∷ xs) | eq = remove-all x xs
  remove-all n (x ∷ xs) | neq y = x ∷ remove-all n xs

  test-remove-all-1 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-all-1 = refl

  test-remove-all-2 : count 5 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-all-2 = refl

  test-remove-all-3 : count 4 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 2
  test-remove-all-3 = refl

  test-remove-all-4 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 0
  test-remove-all-4 = refl

  subset : bag → bag → Bool
  subset [] _ = true
  subset (a ∷ as) [] = false
  subset (a ∷ as) bs = member a bs andb subset as (remove-one a bs)

  test-subset-1 : subset (1 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ true
  test-subset-1 = refl

  test-subset-2 : subset (1 ∷ 2 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ false
  test-subset-2 = refl

  open import Data.Empty

  my-theorem : ∀ b x → count x (add x b) ≡ S (count x b)
  my-theorem b x with eq?ℕ x x
  my-theorem b x | eq = refl
  my-theorem b x | neq y = ⊥-elim (y refl)

{- Reasoning about lists -}

  []++ : ∀ {l} → [] ++ l ≡ l
  []++ = refl

  tail-length-pred : ∀ {l} → pred (length l) ≡ length (tail l)
  tail-length-pred {[]} = refl
  tail-length-pred {x ∷ xs} = refl

  ++-assoc : ∀ {l1 l2 l3} → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
  ++-assoc {[]} = refl
  ++-assoc {x ∷ xs} {l2} {l3} rewrite ++-assoc {xs} {l2} {l3} = refl

  ++-length : ∀ {l1 l2} → length (l1 ++ l2) ≡ length l1 + length l2
  ++-length {[]} = refl
  ++-length {x ∷ xs} {l2} rewrite ++-length {xs} {l2} = refl

  snoc : [ℕ] → ℕ → [ℕ]
  snoc [] v = v ∷ []
  snoc (x ∷ xs) v = x ∷ snoc xs v

  rev : [ℕ] → [ℕ]
  rev [] = []
  rev (x ∷ xs) = snoc (rev xs) x

  test-rev-1 : rev (1 ∷ 2 ∷ 3 ∷ []) ≡ (3 ∷ 2 ∷ 1 ∷ [])
  test-rev-1 = refl

  test-rev-2 : rev [] ≡ []
  test-rev-2 = refl

  length-snoc : ∀ {n l} → length (snoc l n) ≡ S (length l)
  length-snoc {n} {[]} = refl
  length-snoc {n} {x ∷ xs}
    rewrite length-snoc {n} {xs}
    = refl

  rev-length : ∀ {l} → length (rev l) ≡ length l
  rev-length {[]} = refl
  rev-length {x ∷ xs}
    rewrite length-snoc {x} {rev xs}
    = cong S (rev-length {xs})

{- List exercises, part 1 -}

  ++[] : ∀ {l} → l ++ [] ≡ l
  ++[] {[]} = refl
  ++[] {x ∷ xs} rewrite ++[] {xs} = refl

  rev-snoc : ∀ {n l} → rev (snoc l n) ≡ n ∷ (rev l)
  rev-snoc {n} {[]} = refl
  rev-snoc {n} {x ∷ xs}
    rewrite rev-snoc {n} {xs}
    = refl

  rev-involutive : ∀ {l} → rev (rev l) ≡ l
  rev-involutive {[]} = refl
  rev-involutive {x ∷ xs}
    rewrite rev-snoc {x} {rev xs}
    | rev-involutive {xs}
    = refl

  snoc-++ : ∀ {l1 l2 n} → snoc (l1 ++ l2) n ≡ l1 ++ snoc l2 n
  snoc-++ {[]} = refl
  snoc-++ {x ∷ xs} {l2} {n} rewrite snoc-++ {xs} {l2} {n} = refl

  rev-++ : ∀ {l1 l2} → rev (l1 ++ l2) ≡ rev l2 ++ rev l1
  rev-++ {[]} {l2} =  sym (++[] {rev l2})
  rev-++ {x ∷ xs} {l2}
    rewrite rev-++ {xs} {l2}
    | snoc-++ {rev l2} {rev xs} {x}
    = refl

  ++-assoc-4 : ∀ {a b c d} → a ++ (b ++ (c ++ d)) ≡ ((a ++ b) ++ c) ++ d
  ++-assoc-4 {a} {b} {c} {d}
    rewrite ++-assoc {a ++ b} {c} {d}
    | sym (++-assoc {a} {b} {c ++ d})
    = refl

  snoc≡++ : ∀ {l n} → snoc l n ≡ l ++ (n ∷ [])
  snoc≡++ {[]} = refl
  snoc≡++ {x ∷ xs} {n} rewrite snoc≡++ {xs} {n} = refl

  non-zeros-++ : ∀ {l1 l2} → non-zeros (l1 ++ l2) ≡ non-zeros l1 ++ non-zeros l2
  non-zeros-++ {[]} = refl
  non-zeros-++ {O ∷ xs} {l2} = non-zeros-++ {xs} {l2}
  non-zeros-++ {S n ∷ xs} {l2}
    rewrite non-zeros-++ {xs} {l2}
    = refl

  my-theorem-2 : ∀ {l x y} → snoc (x ∷ l) y ≡ x ∷ (l ++ (y ∷ []))
  my-theorem-2 {l} {x} {y}
    rewrite snoc≡++ {l} {y}
    = refl

  count-mem-≠0 : ∀ {s} → 1 ≤ℕ? count 1 (1 ∷ s) ≡ true
  count-mem-≠0 {s} = refl

  n≤ℕ?Sn : ∀ {n} → n ≤ℕ? S n ≡ true
  n≤ℕ?Sn {O} = refl
  n≤ℕ?Sn {S n} = n≤ℕ?Sn {n}

  remove-decreases-count : ∀ {s} → count 0 (remove-one 0 s) ≤ℕ? count 0 s ≡ true
  remove-decreases-count {[]} = refl
  remove-decreases-count {x ∷ xs} with eq?ℕ 0 x
  remove-decreases-count {.0 ∷ xs} | eq = n≤ℕ?Sn {count 0 xs}
  remove-decreases-count {x ∷ xs} | neq y with x
  remove-decreases-count {x ∷ xs} | neq y | O with y refl
  ... | ()
  remove-decreases-count {x ∷ xs} | neq y | S n
    = remove-decreases-count {xs}

  count-++ : ∀ {x l p} → count x (l ++ p) ≡ count x l + count x p
  count-++ {x} {[]} = refl
  count-++ {x} {x' ∷ xs} with eq?ℕ x x'
  count-++ {.x'} {x' ∷ xs} {p} | eq
    rewrite count-++ {x'} {xs} {p} = refl
  count-++ {x} {x' ∷ xs} {p} | neq y = count-++ {x} {xs} {p}

  rev-injective : ∀ {l1 l2} → rev l1 ≡ rev l2 → l1 ≡ l2
  rev-injective {[]} {[]} _ = refl
  rev-injective {[]} {x ∷ xs} r≡r = {!!}
  rev-injective {x ∷ xs} {l2} r≡r = {!!}
