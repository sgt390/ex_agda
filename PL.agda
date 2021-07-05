---
--- Zanatta Stefano
--- 1236595
--- Università di Padova
---

-- While language
-- The language is described here: http://profs.sci.univr.it/~merro/files/WhileExtra_l.pdf
-- The Syntax is on page 3 (I just used the syntax, ignoring all the rest)
-- I implemented the operational semantics for the language
-- The syntax is a bit ugly, but I wanted to keep it simple


-- SYNTAX

-- In the (untyped) While Language we have Naturals and Booleans
-- We can perform operations both on ℕ (e.g. +, ≤) and on 𝔹 (e.g. &, ¬).
-- We have the if_then_else  and while_repeat flow control statements
-- Programs in While language may not terminate (while true repeat skip)
-- Variables are defined by the "location" (𝕃) terms
-- Each location is associated with stores an Integer
-- Locations can be
--      ∘ read:     ! l₁
--      ∘ written:  l₁ ← (Eℕ 3)


-- Auxiliary data
data 𝔹 : Set where
    true  : 𝔹
    false : 𝔹

infix 30 ℕ 
data ℕ : Set where
    zero    : ℕ
    succ    : ℕ → ℕ

infixl 7 _×_
data _×_ (A B : Set) : Set where
  <_,_> : A -> B -> A × B

fst : {A B : Set} -> A × B -> A
fst < x , y > = x

snd : {A B : Set} -> A × B -> B
snd < x , y > = y

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero   + m = m
succ k + m = succ (k + m)



infixl 5 _≤_
_≤_ : ℕ → ℕ → 𝔹
zero  ≤   zero     = true
zero ≤    (succ m) = true
(succ n) ≤ zero     = false
(succ n) ≤ (succ m) =  n ≤ m


infixr 5 List
data List (A : Set) : Set where
    []      : List A
    _∷_     : A → List A → List A

data ⊥ : Set where

data Maybe (A : Set) : Set where
    Nothing : Maybe A
    Just    : A → Maybe A


_≡₈_ : 𝔹 → 𝔹 → 𝔹
true ≡₈ true = true
true ≡₈ false = false
false ≡₈ true = false
false ≡₈ false = true


¬_ : 𝔹 → 𝔹
¬ true  = true
¬ false = true

_&_ : 𝔹 → 𝔹 → 𝔹
true & true = true
true & false = false
false & true = false
false & false = false


-- While language Semantics

-- locations
data 𝕃 : Set where
    first : 𝕃
    there : 𝕃 → 𝕃



infixl 5 Expr
data Expr : (A : Set) → Set where
    Eℕ                  : ℕ → Expr ℕ
    E𝔹                  : 𝔹 → Expr 𝔹
    Eif_then_else_      : {A : Set} → Expr 𝔹 → Expr A → Expr A → Expr A
    Ewhile_repeat_      : {A : Set} → Expr 𝔹 → Expr A → Expr A
    skip                : Expr ⊥
    _←_                 : 𝕃 → Expr ℕ → Expr ℕ
    !_                  : 𝕃 → Expr ℕ
    _+ₑ_                : Expr ℕ → Expr ℕ → Expr ℕ
    _≤ₑ_                : Expr ℕ → Expr ℕ → Expr 𝔹
    _,_                 : {A : Set} → Expr A → Expr A → Expr A
    _≡ₑ_                : Expr 𝔹 → Expr 𝔹 → Expr 𝔹
    ¬ₑ_                  : Expr 𝔹 → Expr 𝔹
    _&ₑ_                 : Expr 𝔹 → Expr 𝔹 → Expr 𝔹
    

-- Some examples of expressions in While Language:
-- assignment: l₁ = 0
_ : Expr ℕ
_ = (there first) ← (Eℕ zero) 

-- if then else
_ : Expr ℕ
_ = Eif (E𝔹 true) then (! (there first)) else (Eℕ (succ zero))

-- operations on locations
_ : Expr ℕ
_ = ((there (there first)) ← ((Eℕ (succ zero)) +ₑ (Eℕ (succ (succ zero)))))  , ((! (there (there first))) +ₑ (Eℕ (succ zero)))

-- infinite cycle
_ : Expr ⊥
_ = Ewhile (E𝔹 true) repeat (skip)

-- SEMANTICS OF WHILE LANGUAGE

-- simple boolean equality function just for 𝕃
_≡ₗ_ : 𝕃 → 𝕃 → 𝔹
first ≡ₗ first = true
first ≡ₗ there y = false
there x ≡ₗ y = x ≡ₗ y


-- extract the location content from the environment
extract : 𝕃 → List (𝕃 × ℕ) → Maybe ℕ
extract l [] = Nothing
extract l (t ∷ env) with l ≡ₗ (fst t)
... | true = Just (snd t)
... | false = extract l env

-- may not terminate (e.g. see the example term "infinite cycle" above) 
{-# NON_TERMINATING #-} 
execute : {A : Set} → Expr A → List (𝕃 × ℕ) → (Maybe A × List (𝕃 × ℕ))
-- ℕatural numbers
execute (Eℕ x) env = < Just x , env >
-- 𝔹ooleans
execute (E𝔹 x) env = < Just x , env >
-- If then else
execute (Eif b then x else y) env with execute b env
... | < Just true , env₁ > = execute x env₁
... | < Just false , env₁ > = execute y env₁
... | < Nothing , env₁ > = < Nothing , env₁ >
-- While repeat
execute (Ewhile b repeat x) env with execute b env
... | < Just true , env₁ > = execute (Ewhile b repeat x) (snd (execute x env₁))
... | < Just false , env₁ > = < Nothing , env₁ >
... | < Nothing , env₁ > = < Nothing , env₁ >
-- skip
execute skip env = < Nothing , env >
-- Assignment to location
execute (l ← x) env with execute x env
... | < Just n , env₁ > = < Just n , (< l , n > ∷ env ) >
... | < Nothing , env₁ > = < Nothing , env >
-- Read a location
execute (! x) env with extract x env
... | y = < y , env >
-- Sum
execute (x +ₑ y) env with execute x env
... | < Nothing , env₁ > = < Nothing , env₁ >
... | < Just x₁ , env₁ > with execute y env₁
... | < Just y₁ , env₂ > = < Just (x₁ + y₁) , env₂ >
... | < Nothing , env₂ > = < Nothing , env₂ >
-- ≤ relation
execute (x ≤ₑ y) env with execute x env
... | < Nothing , env₁ > = < Nothing , env₁ >
... | < Just x₁ , env₁ > with execute y env₁
... | < Just y₁ , env₂ > = < Just (x₁ ≤ y₁) , env₂ >
... | < Nothing , env₂ > = < Nothing , env₂ >
-- Concatenate
execute (x , y) env with execute x env
... | < x₁ , env₁ > = execute y env₁

execute (x ≡ₑ y) env with execute x env
... | < Nothing , env₁ > = < Nothing , env₁  >
... | < Just x₁ , env₁ > with execute y env₁
... | < Nothing , env₂ > = < Nothing  , env₂  >
... | < Just y₁ , env₂ > = < Just (x₁ ≡₈ y₁)  , env₂  >


execute (¬ₑ x) env with execute x env
... | < Just x₁ , env₁ > = < Just (¬ x₁) , env₁ >
... | < Nothing , env₁ > = < Nothing , env₁ >


execute (x &ₑ y) env with execute x env
... | < Nothing , env₁ > = < Nothing , env₁  >
... | < Just x₁ , env₁ > with execute y env₁
... | < Nothing , env₂ > = < Nothing  , env₂  >
... | < Just y₁ , env₂ > = < Just (x₁ & y₁)  , env₂  >




-- TESTING THE PROGRAM

exp₁ : Expr ℕ
exp₁ = Eif (E𝔹 true) then (! (there first)) else (Eℕ (succ zero))

res₁ = execute exp₁ []

