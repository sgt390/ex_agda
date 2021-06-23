-- simply typed lambda calculus
-- (the hello world of agda)

{-
 Examples of lambda terms:

    λx. x       (this denotes the identity) (x ∣→ x) (λ x → x)
    λx. (λy. y)
    λx. (λy.x)
    z           does not make sense alone
    f x         only make sense when f and x are def.

    In pure untyped lambda calculus, we have just the following ingredients:
    - variables     "z"
    - application   "f x"
    - abstraction   "λx. ....."

    A famous extension adds the following ingredients:
    - zero
    - succ

    In the simply-typed lambda calculus, every term must be well-typed,
    there are the following types available:
    - a base type, typically written "*", denoting the nats
    - function types: if τ and τ' are types, so it is (τ ⇒ τ').
    (there is no recursion!! - we can extend it to a version
    that supports recursion)
-}


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ




-- the Agda datatype of possible types in STLC
data Ty : Set where
    *       : Ty
    _⇒_    : Ty → Ty → Ty

Set[_]  : Ty → Set
Set[ * ]        = ℕ
Set[ τ ⇒ τ' ]  = Set[ τ' ] → Set[ τ' ]

-- the Agda datatype of possible variable contexts in STLC
data Cxt : Set where
    ε   : Cxt
    _,_ : Cxt → Ty → Cxt

exampleCxt : Cxt
exampleCxt = (((ε , *) , *) , (* ⇒ *) )

-- how can a type occur in a context? 
-- lists a variable of type τ
data _∈_ : Ty → Cxt → Set where
    here    : {τ : Ty} {Γ : Cxt} → τ ∈ (Γ , τ)
    there   : {τ τ' : Ty} {Γ : Cxt} → τ ∈ Γ → τ ∈ (Γ , τ')



-- "Term Γ τ" is the Agda datatype of STLC terms of type τ in the contect Γ
data Term : Cxt → Ty → Set where
    zero    : {Γ : Cxt} → Term Γ *
    succ    : {Γ : Cxt} → Term Γ (* ⇒ *)
    var     : {Γ : Cxt} → {τ : Ty} → (τ ∈ Γ) → Term Γ τ
    _·_ : {Γ : Cxt} {τ τ' : Ty} → Term Γ (τ ⇒ τ') → Term Γ τ → Term Γ τ'
    lam : {Γ : Cxt} {τ τ' : Ty} → Term (Γ , τ) τ' → Term Γ (τ ⇒ τ')


-- "var zero" refers the most recently added variable
-- "var (succ zero)" refers the second recently added variable
-- problem: using just a ℕ number, we can exceed the number of variables,
-- and we are not sure if the type of the indexed element is in fact τ.
--    var     : {Γ : Cxt} → {τ : Ty} → ℕ → Term Γ τ
-- this is why we change ℕ with the witnesses that τ ∈ Γ

-- Identity
I : Term ε (* ⇒ *)
I = lam (var here)
-- λ x.x

-- lambda lambda of variable(1) ∈ (variable(0), variable(1))
K : {τ τ' : Ty} → Term ε (τ ⇒ (τ' ⇒ τ ))
K = lam (lam (var (there here)))
-- λx . (λy . x)

-- de Bruijn approach ↑

-- proj : parser in agda to rewrite things in de Brujin to normal lambda calculus.

-- "Env Γ" is the Agda datatye of the environments for the content Γ.
-- Such an environment should contain values for each variable occuring in Γ.
data Env : Cxt → Set where
    ∅   : Env ε
    _,_     : {Γ : Cxt} {τ : Ty} → Env Γ → Set[ τ ] → Env (Γ , τ)

-- This is a form of heterogenous lists

{-
    eval : Term Γ τ → Env Γ → Set[ τ ]

    -- we could chose ε instead of Γ but it's less general

    "eval I should be the Agda identity function (λ x → x)"
    "eval K should be the Agda identity function (λ x → (λ y → x))"
-}

lookup : {Γ : Cxt} {τ : Ty} → Env Γ → τ ∈ Γ → Set[ τ ]
lookup (env , x) here = x
lookup (env , _) (there v) = lookup env v

eval : {Γ : Cxt} {τ : Ty} → Term Γ τ → Env Γ → Set[ τ ]
eval zero       env = zero
eval succ       env = succ
eval (var x)    env = lookup env x
eval (s · t)    env = {!  (eval s env) (eval t env) !}
eval (lam t)    env = {! λ x → eval t (env , x) !}



id : ℕ → ℕ
id = eval I ∅

id' : ℕ → ℕ
id' n = n


-- open problem: this example for ML type theory 
