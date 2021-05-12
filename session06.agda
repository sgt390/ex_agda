infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

-- Goal: Define sort : ??? → List A → List A.

module Implementation
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- Given an ordered list "ys",
  -- "insert x ys" is the same as "ys",
  -- but with "x" inserted at the correct place
  -- to ensure that the resulting list is again ordered.
  insert : (x : A) → List A → List A
  insert x []       = x ∷ []
  insert x (y ∷ ys) with cmp x y
  ... | left  x≤y = x ∷ y ∷ ys
  ... | right y≤x = y ∷ insert x ys

  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)

-- TWO METHODS FOR VERIFYING CORRECTNESS:
-- (a) first implement, then separately verify correctness
-- (b) correct by construction

module Verification₁ {A : Set} (_≤_ : A → A → Set) (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Implementation _≤_ cmp

  data IsOrdered : List A → Set where
    empty     : IsOrdered []
    singleton : {x : A} → IsOrdered (x ∷ [])
    cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ y ∷ ys)

  lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered (y ∷ insert x ys)
  lemma₀ x y []       y≤x p = cons y≤x singleton
  lemma₀ x y (z ∷ ys) y≤x (cons y≤z q) with cmp x z
  ... | left  x≤z = cons y≤x (cons x≤z q)
  ... | right z≤x = cons y≤z (lemma₀ x z ys z≤x q)

  lemma : (x : A) (ys : List A) → IsOrdered ys → IsOrdered (insert x ys)
  lemma x []       p = singleton
  lemma x (y ∷ ys) p with cmp x y
  ... | left  x≤y = cons x≤y p
  ... | right y≤x = lemma₀ x y ys y≤x p

  theorem : (xs : List A) → IsOrdered (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)

  cheatsort : List A → List A
  cheatsort xs = []

  cheattheorem : (xs : List A) → IsOrdered (cheatsort xs)
  cheattheorem xs = empty

module Verification₂ {A : Set} (_≤_ : A → A → Set) (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where
  open Implementation _≤_ cmp

  -- (x ◂ ys ↝ xys) should the be the type of witnesses that inserting "x" into "ys" somewhere
  -- yields the list "xys".     -- ◂\t  ↝\leadsto
  data _◂_↝_ : A → List A → List A → Set where
    here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
    there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)

  data IsPerm : List A → List A → Set where
    empty : IsPerm [] []
    cons  : {x : A} {xs ys xys : List A} → (x ◂ ys ↝ xys) → IsPerm xs ys → IsPerm (x ∷ xs) xys

  example : (x y z : A) → IsPerm (x ∷ y ∷ z ∷ []) (z ∷ x ∷ y ∷ [])
  example x y z = cons (there here) (cons (there here) (cons here empty))

  lemma : (x : A) (ys : List A) → x ◂ ys ↝ insert x ys
  lemma x []       = here
  lemma x (y ∷ ys) with cmp x y
  ... | left  x≤y = here
  ... | right y≤x = there (lemma x ys)

  theorem : (xs : List A) → IsPerm xs (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = cons (lemma x (sort xs)) (theorem xs)

module CorrectByConstruction₁ 
    {A : Set} (_≤_ : A → A → Set)
    (min : A) (min≤ : {x : A} → min ≤ x)
    (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  -- "OList l" is the type of ordered lists of elements of A which are bounded from below by l.
  data OList (l : A) : Set where
    nil  : OList l
    cons : (x : A) → l ≤ x → OList x → OList l

  toList : {l : A} → OList l → List A
  toList nil           = []
  toList (cons x _ xs) = x ∷ toList xs

  insert : {l : A} → (x : A) → l ≤ x → OList l → OList l
  insert x l≤x nil             = cons x l≤x nil
  insert x l≤x (cons y l≤y ys) with cmp x y
  ... | left  x≤y = cons x l≤x (cons y x≤y ys)
  ... | right y≤x = cons y l≤y (insert x y≤x ys)

  sort : List A → OList min
  sort []           = nil
  sort (x ∷ xs)     = insert x min≤ (sort xs)