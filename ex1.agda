{-# OPTIONS --without-K #-}
{-
  AGDA IN PADOVA, EXERCISE SHEET 1
  (available in any Agdapad session as "Ex-1.agda")

  Main goal: learn to be comfortable with basic principles of Agda.

  Ingo's secret hope: to find lots of questions in his inbox (iblech@speicherleck.de).
  Ingo's bonus secret hope: to find lots of suggestions for topics to cover in his inbox.

  On the immediate agenda for the future are the following items:
  * nicer notation for calculational proofs
  * dealing with relations and decidability
  * working with lists and vectors and so on

  Once we all feel comfortable with that, we will progress to:
  * (your topic could be listed here! drop me a line! You want the course to be more
    theoretical? We can do that! You want the course to be more
    practically-minded? We can do that too! Tell me your preferences :-))
  * exploring logical laws: de Morgan, law of excluded middle, ...
  * conceptual framework for proofs dealing with computations in rings
  * exploring the type Set and its higher variants Set₁
  * meditating on Russell's paradox
  * lambda calculus
  * "sets as trees"
  * setoids; appreciating the term "setoid hell"
-}


-- DEFINITION OF NATURAL NUMBERS, LISTS, VECTORS AND SOME OPERATIONS

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

two : ℕ
two = succ (succ zero)

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


-- BASIC LEMMAS ABOUT ADDITION AND MULTIPLICATION
-- NOTE: We will learn much nicer syntax for those calculational proofs!

lemma-+-zero : (n : ℕ) → (n + zero ≡ n)
lemma-+-zero zero     = refl
lemma-+-zero (succ k) = cong succ (lemma-+-zero k)
-- Retracing our thinking which lead to this proof:
-- 1. The goal was "(succ k) + zero ≡ succ k".
-- 2. Agda automatically rewrites this goal to "succ (k + zero) ≡ succ k",
--    since the left-hand side can be reduced, employing the definition of _+_.
-- 3. The recursive call "lemma-+-zero k" yields a witness of "k + zero ≡ k".
-- 4. Applying the congruence lemma yields the desired witness of "succ (k + zero) ≡ succ k".

lemma-+-succ : (n m : ℕ) → (n + succ m ≡ succ (n + m))
lemma-+-succ zero     m = refl
lemma-+-succ (succ k) m = cong succ (lemma-+-succ k m)

lemma-+-commutative : (n m : ℕ) → (n + m ≡ m + n)
lemma-+-commutative zero m     = symm (lemma-+-zero m)
lemma-+-commutative (succ k) m = trans (cong succ (lemma-+-commutative k m)) (symm (lemma-+-succ m k))
{-
  Alternatively, the proof could be spelled out as follows:

  lemma-+-commutative (succ k) m = trans q r
    where
    -- goal: succ (k + m) ≡ m + succ k

    p : k + m ≡ m + k
    p = lemma-commutative k m
    
    q : succ (k + m) ≡ succ (m + k)
    q = cong succ p
    
    r : succ (m + k) ≡ m + succ k
    r = symm (lemma-succ m k)
-}

-- EXERCISE: Prove that pred (succ n) is n again.
lemma-pred-succ : (n : ℕ) → pred (succ n) ≡ n
lemma-pred-succ n = refl

-- EXERCISE: Prove these.
_ : two · two ≡ four
_ = refl

_ : two + two ≡ four
_ = refl

-- EXERCISE: Prove that addition is associative.
-- (This will be less involved than the proof of commutativity!)
lemma-+-associative : (a b c : ℕ) → (a + (b + c) ≡ (a + b) + c)
lemma-+-associative zero      b c = refl
-- lemma-+-associative (succ a') b c = cong succ (lemma-+-associative a' b c)
lemma-+-associative (succ a') b c = begin
  succ a' + (b + c)   ≡⟨⟩
  succ (a' + (b + c)) ≡⟨ cong succ (lemma-+-associative a' b c) ⟩
  succ ((a' + b) + c) ≡⟨⟩
  succ (a' + b) + c   ≡⟨⟩   -- \==\<\>
  (succ a' + b) + c   ∎     -- \qed

-- EXERCISE: Show m + (n + p) = n + (m + p).
-- (No induction/recursion needed, just a combination of earlier lemmas.)
-- (This will be ugly to write because we didn't yet cover nice syntax for
-- calculational proofs.)
lemma-+-swap : (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
lemma-+-swap m n p = begin
  m + (n + p) ≡⟨ lemma-+-associative m n p ⟩
  (m + n) + p ≡⟨ cong (λ z → z + p) (lemma-+-commutative m n) ⟩
  (n + m) + p ≡⟨ symm (lemma-+-associative n m p) ⟩
  n + (m + p) ∎

lemma-+-swap' : (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
lemma-+-swap' m n p = trans (lemma-+-associative m n p) (trans (cong (λ z → z + p) (lemma-+-commutative m n)) (symm (lemma-+-associative n m p)))

-- EXERCISE: Prove that multiplication distributes over addition.
lemma-distributive : (a b c : ℕ) → (a + b) · c ≡ a · c + b · c
lemma-distributive a zero c = {! cong (λ x → x · c + zero) (lemma-+-zero a)  !}
lemma-distributive a (succ b) c = {!   !}

-- EXERCISE: Prove that multiplication is associative.
lemma-·-associative : (a b c : ℕ) → (a · (b · c) ≡ (a · b) · c)
lemma-·-associative a b c = {!!}

-- EXERCISE: Prove that multiplication is commutative.
lemma-·-zero : (n : ℕ) → n · zero ≡ zero
lemma-·-zero n = {!!}

lemma-·-succ : (n m : ℕ) → n · succ m ≡ n + n · m
lemma-·-succ n m = {!!}

lemma-·-commutative : (n m : ℕ) → (n · m ≡ m · n)
lemma-·-commutative n m = {!!}


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
succ' xs = {!!}

-- EXERCISE: Define the encoding function.
encode : ℕ → Bin
encode n = {!!}


-- SOME FUNCTIONS ON LISTS AND VECTORS

-- EXERCISE: Define a function which sums the numbers of a given list
sum : List ℕ → ℕ
sum []       = {!!}
sum (x ∷ xs) = {!!}

-- EXERCISE: Define a function which computes the list of the first k values of
-- a given function, in reverse order. For instance: take' two f ≡ f one ∷ f zero ∷ [].
take' : {A : Set} → ℕ → (ℕ → A) → List A
take' n f = {!!}

-- EXERCISE: Define the "head" function, which returns the first element
-- of a vector of positive length.
head : {A : Set} {n : ℕ} → Vector A (succ n) → A
head xs = {!!}

-- EXERCISE: Define the "tail" function, which returns the tail vector
-- of a vector of positive length. For instance, "tail (x ∷ y ∷ z ∷ []) = y ∷ z ∷ []".
-- What should the type signature be?
tail : {!!}
tail = {!!}

-- EXERCISE: Define the "map" function.
-- For instance, "map f (x ∷ y ∷ z ∷ []) = f x ∷ f y ∷ f z ∷ []".
map : {A B : Set} {n : ℕ} → (A → B) → Vector A n → Vector B n
map f xs = {!!}

-- EXERCISE: Define these vector functions.
zipWith : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWith f xs ys = {!!}

drop : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
drop k xs = {!!}

take : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
take k xs = {!!}

_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
xs ++ ys = {!!}

-- snoc (x ∷ y ∷ []) a should be x ∷ y ∷ a ∷ [].
snoc : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snoc xs y = {!!}

one : ℕ
one = succ zero

[_] : {A : Set} → A → Vector A one
[ x ] = x ∷ []

lemma : (n : ℕ) → n + one ≡ succ n
lemma n = begin
  n + one ≡⟨ lemma-+-commutative n one ⟩
  one + n ≡⟨⟩
  succ n  ∎

-- coerce : {A : Set} {n : ℕ} → Vector A (n + one) → Vector A (succ n)
-- coerce {A} {n} xs with n + one with lemma n
-- ... | .(succ n) | refl = xs
-- ... | m | p = ?  -- then do a case split on p

{-# BUILTIN EQUALITY _≡_ #-}

coerce' : {A : Set} {n : ℕ} → Vector A (n + one) → Vector A (succ n)
-- coerce' {A} {n} xs rewrite lemma n = xs
coerce' {A} {n} xs rewrite lemma n = xs

transport : {A : Set} {B : A → Set} {x y : A} → x ≡ y → B x → B y
transport = {!!}

coerce'' : {A : Set} {n : ℕ} → Vector A (n + one) → Vector A (succ n)
coerce'' {A} {n} = transport {ℕ} {Vector A} (lemma n)

-- reverse (x ∷ y ∷ z ∷ []) should be z ∷ y ∷ x ∷ [].
reverse : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverse []       = []
-- reverse (x ∷ xs) = snoc (reverse xs) x
reverse (x ∷ xs) = coerce' (reverse xs ++ [ x ])
-- the computed length of "reverse xs ++ [ x ]" is n + one
-- the expected length is succ n

concat : {A : Set} {n m : ℕ} → Vector (Vector A n) m → Vector A (m · n)
concat xss = {!!}


-- PROPERTIES OF VECTOR FUNCTIONS

lemma-reverse-snoc : {A : Set} {n : ℕ} → (xs : Vector A n) (x : A) → reverse (snoc xs x) ≡ (x ∷ reverse xs)
lemma-reverse-snoc xs x = {!!}

lemma-reverse-reverse : {A : Set} {n : ℕ} → (xs : Vector A n) → reverse (reverse xs) ≡ xs
lemma-reverse-reverse xs = {!!}

lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vector A (k + n)) → take k xs ++ drop k xs ≡ xs
lemma-take-drop k xs = {!!}


-- TASK: Define "<" on natural numbers.

-- Approach I: the "Boolean way"

data Bool : Set where
  false true : Bool

is-<? : ℕ → ℕ → Bool
is-<? zero     zero     = false
is-<? zero     (succ m) = true
is-<? (succ n) zero     = false
is-<? (succ n) (succ m) = is-<? n m

lemma-succ-pred : (n : ℕ) → (is-<? zero n ≡ true) → succ (pred n) ≡ n
lemma-succ-pred (succ n) p = refl


-- Approach II: the "witness-based way"

-- Idea: introduce a type "n < m" of witnesses that n is less than m.

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ} → zero < succ n
  step : {n m : ℕ} → n < m → succ n < succ m

_ : two < four
_ = step (step base)

data ⊥ : Set where

_ : one < zero → ⊥
_ = λ ()

lemma-succ-pred' : (n : ℕ) → zero < n → succ (pred n) ≡ n
lemma-succ-pred' (succ k) p = refl


-- TEASER TEASER TEASER

halve : ℕ → ℕ
halve zero            = zero
halve (succ zero)     = zero
halve (succ (succ n)) = succ (halve n)

{-
-- should compute the number of binary digits, for instance digits 6 should be 3
-- (as 6 is 110 in binary)
digits : ℕ → ℕ
digits zero = zero
digits n    = succ (digits (halve n))
-- Agda highlights this in red, because it does not recognize that this definition
-- gives rise to a total function. It believes that the function might be trapped
-- in an infinite loop.

-- How to fix this? See session 4 :-)
-}