data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
-- For any types A and B, there is a new type A × B.
-- Its inhabitants are as follows:
-- For any value a : A and for any value b : B,
-- there is a value (a , b) : A × B.
--                 ----^
-- So A × B is the type of pairs!

-- EXERCISE: Prove that "α ∧ β ⇒ α".
conj-eliminationₗ : {α β : Set} → α × β → α
conj-eliminationₗ (x , y) = x

conj-eliminationᵣ : {α β : Set} → α × β → β
conj-eliminationᵣ (x , y) = y

conj-introduction : {α β : Set} → α → β → α × β
conj-introduction x y = x , y
-- conj-introduction = _,_

-- REMARK: There is a thing called "propositional truncation":
-- For any type A, its propositional truncation is a type ∥ A ∥
-- which has the following properties:
-- (1) ∥ A ∥ contains at most one value (more precisely, any two values are the same)
-- (2) A is inhabited if and only if ∥ A ∥ is.

{- TEASER: Here is how we can define the propositional truncation
   in Cubical Agda. :-)

   data ∥_∥ (A : Set) : Set where
     proj  : A → ∥ A ∥
     trunc : (x y : ∥ A ∥) → x ≡ y
-}


data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- It's Haskell's Either type!

-- EXERCISE: Prove "α ⇒ α ∨ β".
disj-introductionₗ : {α β : Set} → α → α ⊎ β   -- \uplus
disj-introductionₗ x = left x

disj-introductionᵣ : {α β : Set} → β → α ⊎ β   -- \uplus
disj-introductionᵣ y = right y

lemma : {α β : Set} → α × β → α ⊎ β
lemma = {!!}

-- How many witnesses are there of the statement "x ≡ y"?


-- How to formalize "∃n. φ(n)" in Agda?
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

foo : {A B : Set} → A × B → Σ A (λ _ → B)
foo (x , y) = x , y

oof : {A B : Set} → Σ A (λ _ → B) → A × B
oof (x , y) = x , y

data ⊥ : Set where

¬_ : Set → Set
¬ A = (A → ⊥)

double-negation-introduction : {A : Set} → A → ¬ ¬ A
double-negation-introduction x = λ f → f x

-- our "ingredients" do not have any "→ A", so it is not possible
-- to fill the hole
-- we ned to postulate
double-negation-elimination : {A : Set} → ¬ ¬ A → A
double-negation-elimination f = {!   !}

fun : {A B : Set} → ¬ ¬ A → ¬ ¬ B → ¬ ¬ (A × B)
fun = {!   !}


-- "¬(α ∨ β) ⇒ (¬α) ∧ (¬β)"
de-morgan₁ : {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
de-morgan₁ f = (λ x → f (left x)) , (λ y → f (right y))

de-morgan₂ : {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
de-morgan₂ (f , g) = λ { (left x) → f x ; (right y) → g y }

de-morgan₃ : {A B : Set} → (¬ (A × B)) → (¬ A) ⊎ (¬ B)
de-morgan₃ = {!   !}  -- this hole cannot be filled without postulates

module _ (LEM : ((X : Set) → X ⊎ (¬ X))) where
  rab : {A : Set} → ¬ ¬ A → A
  rab = {!!}  -- without custom postulates such as LEM above, you will not be able to fill this hole

{-
IsPrime = {!!}
_>_     = {!!}
ℕ       = {!!}

infinitude-of-primes : (n : ℕ) → Σ ℕ (λ p → (IsPrime p) × (p > n))
infinitude-of-primes n = {!!}

-- REMARK:
-- Even if B x contains at most one value for any x : A,
-- the type Σ A B might contain many distinct values.

-}