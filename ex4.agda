-- SIMPLY TYPED LAMBDA CALCULUS
-- (The HELLO WORLD of Agda)

{-
  Examples for lambda terms:

    λx. x         (this denotes the identity function)    (x ↦ x)   (λ x → x)
    λx. (λy. y)   (this denotes a function which
                   ignores its first argument and returns
                   the identity function)
    λx. (λy. x)
    z
    f x
  
  In pure untyped lambda calculus, we have just the following ingredients:
  - variables    "z"
  - application  "f x"
  - abstraction  "λx. ..."

  A famous extension adds the following ingredients:
  - zero : *
  - succ : * ⇒ *
  
  In the simply-typed lambda calculus, every term has to be well-typed, and there
  are the following types available:
  - a base type, typically written "*", denoting the natural numbers
  - function types: if τ and τ' are types, so is (τ ⇒ τ').
-}

open import Data.Nat hiding (pred)

-- the Agda datatype of possible types in STLC
data Ty : Set where
  *   : Ty
  _⇒_ : Ty → Ty → Ty

Set[_] : Ty → Set       -- other usual notation: ⟦_⟧
Set[ * ]      = ℕ
Set[ τ ⇒ τ' ] = Set[ τ ] → Set[ τ' ]

-- the Agda datatype of possible variable contexts in STLC
data Cxt : Set where
  ε   : Cxt
  _,_ : Cxt → Ty → Cxt
-- NB: Cxt is the same as List Ty

exampleCxt : Cxt
exampleCxt = (((ε , *) , *) , (* ⇒ *))

-- "τ ∈ Γ" is the the Agda datatype of witnesses that the context Γ
-- lists a variable of type τ
data _∈_ : Ty → Cxt → Set where
  here  : {τ : Ty}    {Γ : Cxt}         → τ ∈ (Γ , τ)
  there : {τ τ' : Ty} {Γ : Cxt} → τ ∈ Γ → τ ∈ (Γ , τ')
-- enhanced (type/context-aware) de Bruijn approach to variables

-- "Term Γ τ" is the Agda datatype of STLC terms of type τ in the context Γ
data Term : Cxt → Ty → Set where
  zero : {Γ : Cxt} → Term Γ *
  succ : {Γ : Cxt} → Term Γ (* ⇒ *)
  rec  : {Γ : Cxt} {τ : Ty} → Term Γ (τ ⇒ ((* ⇒ (τ ⇒ τ)) ⇒ (* ⇒ τ)))
  var  : {Γ : Cxt} {τ : Ty} → τ ∈ Γ → Term Γ τ
  _·_  : {Γ : Cxt} {τ τ' : Ty} → Term Γ (τ ⇒ τ') → Term Γ τ → Term Γ τ'
  lam  : {Γ : Cxt} {τ τ' : Ty} → Term (Γ , τ) τ' → Term Γ (τ ⇒ τ')

-- in Haskell: infiniteLoop = let x = x in x

exampleFunc : ℕ → ℕ
exampleFunc zero    = 7
exampleFunc (suc n) = n + exampleFunc n

recursor : {A : Set} → A → ((ℕ → (A → A)) → (ℕ → A))
recursor base step zero    = base
recursor base step (suc n) = step n (recursor base step n)

exampleFunc' : ℕ → ℕ
exampleFunc' = recursor 7 (λ n x → n + x)


I : Term ε (* ⇒ *)
I = lam (var here)
-- λx. x

K : {τ τ' : Ty} → Term ε (τ ⇒ (τ' ⇒ τ))
K = lam (lam (var (there here)))
-- λx. (λy. x)

-- "Env Γ" is the Agda datatype of environments for the context Γ.
-- Such an environment should contain values for each variable occurring in Γ.
data Env : Cxt → Set where
  ∅   : Env ε
  _,_ : {Γ : Cxt} {τ : Ty} → Env Γ → Set[ τ ] → Env (Γ , τ)
-- This is a form of heterogenous lists

lookup : {Γ : Cxt} {τ : Ty} → Env Γ → τ ∈ Γ → Set[ τ ]
lookup (env , x) here      = x
lookup (env , _) (there v) = lookup env v

eval : {Γ : Cxt} {τ : Ty} → Term Γ τ → Env Γ → Set[ τ ]
eval zero    env = 0
eval succ    env = suc
eval rec     env = recursor
eval (var v) env = lookup env v
eval (s · t) env = (eval s env) (eval t env)
eval (lam t) env = λ x → eval t (env , x)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

pred' : ℕ → ℕ
pred' = recursor zero (λ n → λ x → n)

predTerm : Term ε (* ⇒ *)
predTerm = (rec · zero) · K

id : ℕ → ℕ
id = eval I ∅

id' : ℕ → ℕ
id' n = n

open import Relation.Binary.PropositionalEquality

_ : id ≡ id'
_ = refl

-- ETA EXPANSION: f ≡ (λ x → f x)

const : ℕ → ℕ → ℕ
const = eval K ∅

{-

  "eval I" should be the Agda identity function (λ x → x)
  "eval K" should be the Agda function (λ x → (λ y → x))
-}

-- EXERCISE: Extend the development by primitive recursion.
-- (By now, this exercise has already been solved in this file.)

-- EXERCISE: Implement an evaluator for a small toy imperative programming language.

-- EXERCISE: Define a "big step" operational semantics.
data _⇓_ {Γ : Cxt} : {τ : Ty} → Term Γ τ → Term Γ τ → Set where
  zero : zero ⇓ zero
  -- ...