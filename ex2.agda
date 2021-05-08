{-
  AGDA IN PADOVA, EXERCISE SHEET 2
  (available in any Agdapad session as "Ex-2.agda")
-}


-- DEFINITION OF NATURAL NUMBERS, LISTS, VECTORS AND SOME OPERATIONS

-- The empty type
data ⊥ : Set where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

pred : ℕ → ℕ   -- predecessor
pred zero     = zero
pred (succ k) = k

infixl 6 _+_  -- the "l" causes Agda to interpret x + y + z as (x + y) + z
_+_ : ℕ → ℕ → ℕ
zero   + m = m
succ k + m = succ (k + m)

-- EXERCISE: Fill in the definition of multiplication.
infixl 7 _·_
_·_ : ℕ → ℕ → ℕ
zero   · m = zero
succ n · m = m + n · m
-- heuristic explanation for definition: succ n · m = (1 + n) · m = m + n · m

one : ℕ
one = succ zero

two : ℕ
two = succ (succ zero)

three : ℕ
three = succ (succ (succ zero))

four : ℕ
four = succ (succ (succ (succ zero)))

exampleList : List ℕ
exampleList = four ∷ two ∷ four ∷ []
-- in Haskell notation: [four, two, four]


-- DEFINITION OF EQUALITY AND BASIC LEMMAS ABOUT EQUALITY

infixl 5 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
--  bailout : {A : Set} {x : A} {y : A} → x ≡ y
-- (x ≡ y) is the type of witnesses that x and y are equal

symm : {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
symm refl = refl

-- EXERCISE: Fill in the hole.
trans : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
trans refl q = q
-- trans refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → (x ≡ y) → (f x ≡ f y)
cong f refl = refl


-- EQUATIONAL REASONING

infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin_

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl


-- A BINARY REPRESENTATION OF NATURAL NUMBERS

-- We here define a more space-efficient representation of natural numbers,
-- not using the unary system but the binary system:
data Bin : Set where
  [] : Bin
  _O : Bin → Bin   -- this is a capital "oh", not the digit zero
  _I : Bin → Bin   -- capital "eye", not the digit 1
-- For instance, the number 6, in binary notation written as 110, is encoded as
-- [] I I O. (This is shorthand for _O (_I (_I [])).
-- This representation is not unique because of the possibility of trailing zeros.
-- We won't mind right now and fix this later.

-- EXERCISE: Define a function Bin → ℕ which decodes the binary representation into
-- actual natural numbers.
decode : Bin → ℕ
decode []     = zero
decode (xs O) = decode xs + decode xs          -- 1100 is twice 110
decode (xs I) = succ (decode xs + decode xs)   -- 1101 is twice 110, and then one more

six : ℕ
six = four + two

_ : decode ([] I I O) ≡ six
_ = refl

-- EXERCISE: Define the successor operation on Bin.
succ' : Bin → Bin
succ' xs = xs

-- EXERCISE: Define the encoding function.
encode : ℕ → Bin
encode n = []


-- SOME FUNCTIONS ON LISTS AND VECTORS

-- EXERCISE: Define a function which computes the length of a given list
length : {X : Set} → List X → ℕ
length []       = zero
length (x ∷ xs) = succ (length xs)

snoc : {X : Set} → List X → X → List X
snoc []       y = y ∷ []
snoc (x ∷ xs) y = x ∷ snoc xs y

reverse : {X : Set} → List X → List X
reverse []       = []
reverse (x ∷ xs) = snoc (reverse xs) x


-- ON FORMALIZING RELATIONS IN AGDA

-- Approach I: the "Boolean way"

data Bool : Set where
  false true : Bool

is-<?' : ℕ → ℕ → Bool
is-<?' zero     zero     = false
is-<?' zero     (succ m) = true
is-<?' (succ n) zero     = false
is-<?' (succ n) (succ m) = is-<?' n m

lemma-succ-pred : (n : ℕ) → (is-<?' zero n ≡ true) → succ (pred n) ≡ n
lemma-succ-pred (succ n) p = refl


-- Approach II: the "witness-based way"
-- Idea: introduce a type "n < m" of witnesses that n is less than m.

data _<'_ : ℕ → ℕ → Set where
  base : {n : ℕ} → zero <' succ n
  step : {n m : ℕ} → n <' m → succ n <' succ m

data _≤_ : ℕ → ℕ → Set where
  base : {n : ℕ} → n ≤ n
  step : {n m : ℕ} → n ≤ m → n ≤ succ m

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ} → n < succ n
  step : {n m : ℕ} → n < m → n < succ m

succ-monotonic : {a b : ℕ} → a < b → succ a < succ b
succ-monotonic base     = base
succ-monotonic (step p) = step (succ-monotonic p)

aux₁ : {a b : ℕ} → succ a < b → a < b
aux₁ base = step base
aux₁ (step x) = step (aux₁ x)


inv-succ-monotonic : {a b : ℕ} → succ a < succ b → a < b
inv-succ-monotonic base     = base
inv-succ-monotonic (step p) = aux₁ p

lemma-<⇒≤ : {a b : ℕ} → a < b → a ≤ b
lemma-<⇒≤ base     = step base
lemma-<⇒≤ (step p) = step (lemma-<⇒≤ p)

-- EXERCISE: Show that _≤_ is transitive.
IsTransitive : {X : Set} (_≤_ : X → X → Set) → Set
IsTransitive _≤_ = {a b c : _} → a ≤ b → b ≤ c → a ≤ c

lemma-≤-transitive : IsTransitive _<_
lemma-≤-transitive p base     = step p
lemma-≤-transitive p (step q) = step (lemma-≤-transitive p q)

-- EXERCISE: Show that _≤_ is antisymmetric.
IsAntiSymm : {X : Set} (_≤_ : X → X → Set) → Set
IsAntiSymm _≤_ = {a b : _} → a ≤ b → b ≤ a → a ≡ b

lemma-≤-antisymm : IsAntiSymm _≤_
lemma-≤-antisymm base b = refl
lemma-≤-antisymm (step a) base = refl
lemma-≤-antisymm (step a) (step b) = cong succ (lemma-≤-antisymm (aux≤ a) (aux≤ b)) where
  aux≤ : {a b : ℕ} → succ a ≤ b → a ≤ b
  aux≤ base = step base
  aux≤ (step x) = step (aux≤ x) 

IsReflexive : {X : Set} (_≤_ : X → X → Set) → Set
IsReflexive _≤_ = {x : _} → x ≤ x

IsSymmetric : {X : Set} (_~_ : X → X → Set) → Set
IsSymmetric _~_ = {x y : _} → x ~ y → y ~ x

-- EXERCISE: Given a binary relation, compute its reflexive symmetric transitive hull.
module _ {X : Set} (R : X → X → Set) where
  data R* : X → X → Set where
    -- fill this in :-)

  R*-is-equivalence-relation₁ : IsReflexive R*
  R*-is-equivalence-relation₂ : IsSymmetric R*
  R*-is-equivalence-relation₃ : IsTransitive R*

  R*-is-equivalence-relation₁ = {!!}
  R*-is-equivalence-relation₂ = λ ()
  R*-is-equivalence-relation₃ = {!!}

  embed : {x y : X} → R x y → R* x y
  embed = {!!}

  universal
    : (S : X → X → Set)
    → IsReflexive S → IsSymmetric S → IsTransitive S
    → ({x y : X} → R x y → S x y)
    → ({x y : X} → R* x y → S x y)
  universal = λ S _ _ _ _ ()


-- TASK: We define a relation expressing that all elements of a list satisfy some
-- predicate P.
--
-- For instance, P could be the function (to be defined) isEven : ℕ → Set.
-- This function should return an inhabited typed for even inputs and an empty type for odd inputs.
--
-- A further example: P = _<_ zero : ℕ → Set. "P n" expresses that n is larger than zero.
-- The type "P n" is the type of witnesses that "zero < n".

-- We picture "All P xs" as the type of witnesses that all elements of the list xs satisfy P.
data All {X : Set} (P : X → Set) : List X → Set where
  nil  : All P []
  cons : {x : X} {xs : List X} → P x → All P xs → All P (x ∷ xs)

example : {X : Set} {P : X → Set} {x y z : X} → P x → P y → P z → All P (x ∷ y ∷ z ∷ [])
example p q r = cons p (cons q (cons r nil))

-- TASK: Define the predicate "Any P xs" expressing that at least one element of xs
-- satisfies P.
data Any {X : Set} (P : X → Set) : List X → Set where
  here  : {x : X} {xs : List X} → P x → Any P (x ∷ xs)
  there : {x : X} {xs : List X} → Any P xs → Any P (x ∷ xs)

-- EXERCISE: The following claim is not provable, because the empty list [] is an exception:
--     alltoany : {X : Set} {P : X → Set} {xs : List X} → All P xs → Any P xs
--     alltoany p = {!!}
-- Show that indeed, such a function alltoany does not exist:

aux-any : {X : Set} {P : X → Set} → Any P [] → ⊥
aux-any = λ ()

lemma-no-naive-alltoany : ({X : Set} {P : X → Set} {xs : List X} → All P xs → Any P xs) → ⊥
lemma-no-naive-alltoany f with (f nil)
... |    any[] = aux-any any[]

-- "NonEmpty xs" is the type of witnesses that the list xs is not empty.
data NonEmpty {X : Set} : List X → Set where
  look : {x : X} {xs : List X} → NonEmpty (x ∷ xs)

alltoany : {X : Set} {P : X → Set} (xs : List X) → NonEmpty xs → All P xs → Any P xs
alltoany (x ∷ xs) look (cons p q) = here p

alltoany' : {X : Set} {P : X → Set} {xs : List X} → zero < length xs → All P xs → Any P xs
alltoany' _ (cons p q) = here p

-- EXERCISE: Define a predicate expressing that all elements of a given list are equal.

-- EXERCISE: Define a predicate expressing that a given list is a palindrome (like x ∷ y ∷ z ∷ y ∷ x ∷ []).
-- There are several ways how this can be done. One approach I can think of uses
-- the function "reverse", another uses "snoc" (both defined above).

-- There is a connection between the boolean way and the witness-based
-- way: For some relations, we can computationally check whether they
-- hold. This notion is formalized as follows:

data Dec (A : Set) : Set where    -- "Dec" is short for "Decidable"
  yes : A → Dec A
  no  : (A → ⊥) → Dec A
-- A value of type "Dec A" expresses that we can decide (computationally)
-- whether A is inhabited or not.

0<succ : (a : ℕ) → zero < succ a
0<succ zero = base
0<succ (succ a) = step (0<succ a)

-- EXERCISE: Show that "_<_" is decidable.
is-<? : (a b : ℕ) → Dec (a < b)
is-<? zero     zero     = no (λ ())
is-<? zero     (succ b) = yes (0<succ b)
is-<? (succ a) zero = no (λ ())
is-<? (succ a) (succ b) with (is-<? a b)
... |    yes x = yes (succ-monotonic x)
... |    no  f = no λ x → f (inv-succ-monotonic x)

-- EXERCISE: Show that "All P" is decidable, if P is.
is-all? : {X : Set} {P : X → Set} → ((x : X) → Dec (P x)) → (xs : List X) → Dec (All P xs)
is-all? oracle []       = yes nil
is-all? oracle (x ∷ xs) with oracle x | is-all? oracle xs
... | yes p | yes q = yes (cons p q)
... | yes p | no  q = no λ { (cons r s) → q s }
... | no  p | q     = no λ { (cons q r) → p q }

{- in Haskell:
  all P [] = True
  all P (x :: xs)
    | P x       = all P xs
    | otherwise = False
-}

-- EXERCISE: Show that "Any P" is decidable, if P is.
-- todo : is there a better way?
is-any? : {X : Set} {P : X → Set} → ((x : X) → Dec (P x)) → (xs : List X) → Dec (Any P xs)
is-any? oracle [] = no (λ ())
is-any? oracle (x ∷ xs) with oracle x
...                     | yes a = yes (here a)
...                     | no a with is-any? oracle xs
...                            | yes a₁ = yes (there a₁)
...                            | no a₁ = no (λ x₁ → aux₂ a a₁ x₁) where -- aux₂ a a₁    where
    aux₂ : {X : Set} {P : X → Set} {x : X} {xs : List X} → (P x → ⊥) → (Any P xs → ⊥) → Any P (x ∷ xs) → ⊥
    aux₂ d₁ d₂ (here x) = d₁ x
    aux₂ d₁ d₂ (there p) = d₂ p



-- ON NOT OBVIOUSLY TERMINATING FUNCTIONS

-- The halving function, for instance "halve four ≡ two" and "halve five ≡ two" (we round down).
halve : ℕ → ℕ
halve zero = zero
halve (succ zero) = zero
halve (succ (succ n)) = succ (halve n)
-- turn any two "succ"'s into just one

_ : halve four ≡ two
_ = refl

_ : halve (succ four) ≡ two
_ = refl

-- This function should compute the number of binary digits of the input.
-- for instance: "digits four" should be three (since four is 100 in binary).
digits : ℕ → ℕ
digits zero = zero
digits n    = succ (digits (halve n))
-- The argument "halve n" in the recursive call is smaller than n, but to Agda
-- it is not obvious that "halve n" is a strict part of n. Hence Agda's termination checker
-- rejects this definition.

-- Four ways to deal with this situation:
-- (1) {-# TERMINATING #-} (this won't work with {-# OPTIONS --safe #-}
-- (2) {-# NON_TERMINATING #-} (this won't work with {-# OPTIONS --safe #-}
-- (3) rewrite function, employ a different algorithm
-- (4) use a poor version of gas
-- (5) use a sophisticated version of gas ("well-founded induction")

-- Option (3)
length' : Bin → ℕ
length' [] = zero
length' (x O) = succ (length' x)
length' (x I) = succ (length' x)

digits' : ℕ → ℕ
digits' n = length' (encode n)

-- Opion (4): use gas (with a hopefully sufficiently high initial amount of gas)
digits'' : ℕ → ℕ
digits'' n = go n n
  where
  go : ℕ → ℕ → ℕ
  go n    zero       = zero   -- (*)
  go zero (succ gas) = zero
  go n    (succ gas) = succ (go (halve n) gas)
-- NOTE: This solution works, but is brittle. It depends on supplying a sufficient
-- amount of initial gas, to ensure that the bailout clause (*) is never reached.
-- This should be proven. Later, proofs about properties of digits'' will always be
-- encumbered by having to deal with gas.

-- The idea with gas is good, but we shouldn't use natural numbers to measure gas.
-- On to option (5)!

-- For a type X and a binary relation _<_ on X, "Acc _<_ x" is the type
-- of witnesses that x is "accessible in an inductive manner".
-- Such a witness allows us to do arbitrary recursive calls with
-- arguments which are less than x.
data Acc {X : Set} (_<_ : X → X → Set) : X → Set where
  -- NOTE: Here "_<_" is an arbitrary relation, not necessarily the relation on natural numbers
  -- which we have defined above.
  acc : {x : X} → ((y : X) → y < x → Acc _<_ y) → Acc _<_ x
    -- The constructor "acc" is saying:
    -- "x is accessible, assuming we have witnesses that each element smaller than x is accessible."

invert : {X : Set} {_<_ : X → X → Set} {x : X} → Acc _<_ x → ((y : X) → y < x → Acc _<_ y)
invert (acc f) = f

-- How can we get off the ground?
zero-acc : Acc _<_ zero
zero-acc = acc (λ y ())
-- There are no natural numbers less than zero. Hence "λ y ()" is a function which
-- input a number y and a witness that (perversely) it is less than
-- zero and outputs a witness that y is accessible.

-- Having established that zero is accessible, we can verify that one is as well:
one-acc : Acc _<_ one
one-acc = acc λ { zero base → zero-acc }

-- Having the accessibility of zero and one established, we can verify that two is accessible:
two-acc : Acc _<_ two
two-acc = acc λ { .(succ zero) base → one-acc ; .zero (step base) → zero-acc }

-- One more :-)
three-acc : Acc _<_ three
three-acc = acc λ { .(succ (succ zero)) base → two-acc ; .(succ zero) (step base) → one-acc ; .zero (step (step base)) → zero-acc }

-- We could continue in this fashion, or verify in one go that any natural number is accessible:

Well-Founded : {X : Set} → (X → X → Set) → Set
Well-Founded _<_ = (x : _) → Acc _<_ x
-- A value of type "Well-Founded _<_" is a witness that any element is accessible.

wf-nat : Well-Founded _<_
wf-nat zero     = acc (λ y ())
wf-nat (succ n) = acc (λ { y base → wf-nat n ; y (step p) → invert (wf-nat n) y p })

-- In classical mathematics, a set X together with a binary relation _<_ on X
-- is well-founded if and only if there are no infinite strictly decreasing chains
-- of elements of X, that is if the following situation does NOT arise:
--     x0 > x1 > x2 > x3 > ...

-- For instance, the natural numbers with the usual ordering _<_ are well-founded.
-- The integers with their usual ordering are NOT well-founded.

lemma-halve-< : (n : ℕ) → halve (succ n) < succ n
lemma-halve-< zero            = base
lemma-halve-< (succ zero)     = base
lemma-halve-< (succ (succ n)) = succ-monotonic (step (lemma-halve-< n))

digits''' : ℕ → ℕ
digits''' n = go n (wf-nat n)
  where
  go : (n : ℕ) → Acc _<_ n → ℕ
  go zero     (acc f) = zero
  go (succ n) (acc f) = succ (go     (halve (succ n)) (f (halve (succ n)) (lemma-halve-< n)))
  -- compare with the original definition:
  -- digits (succ n)  = succ (digits (halve (succ n)))

-- EXERCISE: Prove the following lemma, which looks deceptively simple but is not.
lemma-digits''' : (n : ℕ) → digits''' (succ n) ≡ succ (digits''' (halve (succ n)))
lemma-digits''' zero = refl
lemma-digits''' (succ n) = begin
      digits''' (succ (succ n))                ≡⟨ {! ? !} ⟩
      succ (digits''' (succ (halve n)))        ≡⟨⟩
      succ (digits''' (halve (succ (succ n)))) ∎


-- EXERCISE: Show that well-founded relations are irreflexive. More
-- precisely, verify the following local version of this statement:
lemma-wf-irreflexive : {X : Set} {_<_ : X → X → Set} {x : X} → Acc _<_ x → x < x → ⊥
lemma-wf-irreflexive (acc f) x<x = {! !}


-- EXERCISE: Show that there are no infinite descending sequences.
lemma-no-descending-sequences : {X : Set} {_<_ : X → X → Set} → (α : ℕ → X) → ((n : ℕ) → α (succ n) < α n) → Acc _<_ (α zero) → ⊥
lemma-no-descending-sequences α desc p = {!!}


-- EXERCISE (if you feel adventurous): Implement quicksort.







_ : zero ≡ one → ⊥
_ = λ ()






{--
-- EXERCISE: Show that "All P" is decidable, if P is.
is-all? : {X : Set} {P : X → Set} → ((x : X) → Dec (P x)) → (xs : List X) → Dec (All P xs)
is-all? oracle []       = yes nil
is-all? oracle (x ∷ xs) with oracle x
... | yes p with is-all? oracle xs
...            |   yes q = yes (cons p q)
...            |   no q  = no λ { (cons r s) → q s }
... | no  p              = no λ { (cons q r) → p q }
--}