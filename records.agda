-- A monoid is a set M together with an element e and a binary operator *
-- such that e * x ≡ x and x * e ≡ x and x * (y * z) ≡ (x * y) * z.

infixl 5 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

record Monoid : Set₁ where
  field
    Carrier : Set
    -- _≈_  : Carrier → Carrier → Set
    _*_     : Carrier → Carrier → Carrier   -- in Haskell, <>
    empty   : Carrier                       -- in Haskell, mempty

    associative : (x y z : Carrier) → x * (y * z) ≡ (x * y) * z
    neutralₗ    : (x : Carrier) → empty * x ≡ x
    neutralᵣ    : (x : Carrier) → x * empty ≡ x

record ⊤ : Set where
  -- eta-equality

⋆ : ⊤
⋆ = record {}

-- { ⋆ }
TrivialMonoid : Monoid
TrivialMonoid = record
  { Carrier = ⊤
  ; _*_ = λ x y → ⋆
  ; empty = ⋆
  ; associative = λ x y z → refl
  ; neutralₗ = λ { ⋆ → refl }
  ; neutralᵣ = λ { x → refl }
  }

ListMonoid : (A : Set) → Monoid
ListMonoid A = record
  { Carrier = List
  ; _*_ = _++_
  ; empty = []
  ; associative = {!!}
  ; neutralₗ = λ x → refl
  ; neutralᵣ = {!!}
  }
  where
  data List : Set where
    []  : List
    _∷_ : A → List → List
  _++_ : List → List → List
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Monoid.empty is a function which takes a monoid structure
-- and returns the neutral element of that monoid.

module _ (M : Monoid) (N : Monoid) where
  -- someSpecialElement = (Monoid._*_ M) (Monoid.empty M) (Monoid.empty M)

  open Monoid M
  open Monoid N renaming (Carrier to Carrier'; empty to empty'; _*_ to _*'_)

  someSpecialElement : Carrier   -- or: Monoid.Carrier M
  someSpecialElement = empty * empty

record MonoidHomomorphism (M : Monoid) (N : Monoid) : Set where
  open Monoid M
  open Monoid N renaming (Carrier to Carrier'; empty to empty'; _*_ to _*'_)

  field
    fun             : Carrier → Carrier'
    preserves-*     : (x y : Carrier) → fun (x * y) ≡ fun x *' fun y
    preserves-empty : fun empty ≡ empty'

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

ℕ-Monoid : Monoid
ℕ-Monoid = record
   { Carrier = ℕ
   ; _*_ = {!!}
   ; empty = {!!}
   ; associative = {!!}
   ; neutralₗ = {!!}
   ; neutralᵣ = {!!}
  }

free-morphism : (M : Monoid) (x : Monoid.Carrier M) → MonoidHomomorphism ℕ-Monoid M
free-morphism M x = record
  { fun = {!f!}
  ; preserves-* = {!!}
  ; preserves-empty = {!!}
  }
  where
  f : ℕ → Monoid.Carrier M
  f n = {!!}
-- free-morphism M x is a monoid homomorphism which maps 1 to x
-- (and 2 to x * x, and 3 to x * x * x, ...).

module _ (M : Monoid) (x : Monoid.Carrier M) where
  is-unique : (f : MonoidHomomorphism ℕ-Monoid M) (a : ℕ) → MonoidHomomorphism.fun f a ≡ MonoidHomomorphism.fun (free-morphism M x) a
  is-unique f = {!!}

record Inhabited {A : Set} (P : A → Set) : Set where
  field
    elem  : A
    has-P : P elem
-- A value of type "Inhabited P" is a witness that, for some element "elem" of A, the type
-- "P elem" is inhabited.
-- equivalently: Inhabited P = Σ A P

-- Given a predicate P, "minimum P" should be the least natural number which satisfies P.
{-
minimum : (P : ℕ → Set) → Inhabited P → ℕ
minimum = {!!}

minimum-has-P : (P : ℕ → Set) → (p : Inhabited P) → P (minimum P p)
minimum-has-P = {!!}

minimum-is-least : (P : ℕ → Set) → (p : Inhabited P) → (m : ℕ) → P m → minimum P p ≤ m
minimum-is-least = {!!}
-}

_≤_ : ℕ → ℕ → Set
_≤_ = {!!}

record Minimum (P : ℕ → Set) : Set where
  field
    n     : ℕ
    has-P : P n
    least : (m : ℕ) → P m → n ≤ m

minimum : (P : ℕ → Set) → Inhabited P → Minimum P
minimum = {!!}
-- There is no way to fill in this hole, as Agda is a constructive system.

data ⊥ : Set where

data Dec (A : Set) : Set where
  yes : A       → Dec A
  no  : (A → ⊥) → Dec A

minimum' : (P : ℕ → Set) → ((n : ℕ) → Dec (P n)) → Inhabited P → Minimum P
minimum' = {!!}

¬_ : Set → Set
¬ A = A → ⊥

minimum'' : (P : ℕ → Set) → Inhabited P → ¬ ¬ (Minimum P)
minimum'' = {!!}

-- DEFINING THE REAL NUMBERS.
-- Let's have a look of the flavor of the Dedekind reals (there are also the Cauchy reals,
-- the MacNeille reals, the lower reals, the upper reals, ...).

-- A Dedekind real is a Dedekind cut, consisting of a set of rational numbers smaller than the real
-- and a set of rational numbers larger than the real.

open import Data.Rational

record DedekindCut : Set where
  field
    L : ℚ → Set
    U : ℚ → Set
    L-is-inhabited : Σ ℚ L
    U-is-inhabited : Σ ℚ L