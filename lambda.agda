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

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

infixl 6 _+_  -- the "l" causes Agda to interpret x + y + z as (x + y) + z
_+_ : ℕ → ℕ → ℕ
zero   + m = m
suc k + m = suc (k + m)




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
  -- rec  : {Γ : Cxt} {τ : Ty} → Term Γ (....)
  var  : {Γ : Cxt} {τ : Ty} → τ ∈ Γ → Term Γ τ
  _·_  : {Γ : Cxt} {τ τ' : Ty} → Term Γ (τ ⇒ τ') → Term Γ τ → Term Γ τ'
  lam  : {Γ : Cxt} {τ τ' : Ty} → Term (Γ , τ) τ' → Term Γ (τ ⇒ τ')

-- in Haskell: infiniteLoop = let x = x in x

exampleFunc : ℕ → ℕ
exampleFunc zero    = suc (suc (suc zero))
exampleFunc (suc n) = n + exampleFunc n

rec : {A : Set} → A → (ℕ → A → A) → (ℕ → A)
rec base step zero    = base
rec base step (suc n) = step n base

exampleFunc' : ℕ → ℕ
exampleFunc' = rec (suc (suc (suc zero))) (λ n x → n + x)


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
eval zero    env = zero
eval succ    env = suc
eval (var v) env = lookup env v
eval (s · t) env = (eval s env) (eval t env)
eval (lam t) env = λ x → eval t (env , x)

id : ℕ → ℕ
id = eval I ∅

id' : ℕ → ℕ
id' n = n

infixl 5 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

_ : id ≡ id'
_ = refl

-- ETA EXPANSION: f ≡ (λ x → f x)

const : ℕ → ℕ → ℕ
const = eval K ∅

{-

  "eval I" should be the Agda identity function (λ x → x)
  "eval K" should be the Agda function (λ x → (λ y → x))
-}

-- EXERCISES: Extend the development by primitive recursion.
