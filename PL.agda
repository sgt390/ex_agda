---
--- Zanatta Stefano
--- 1236595
--- UniversitΓ  di Padova
---

-- While language
-- The language is described here: http://profs.sci.univr.it/~merro/files/WhileExtra_l.pdf
-- The Syntax is on page 3 (I just used the syntax, ignoring all the rest)
-- I implemented the operational semantics for the language
-- The syntax is a bit ugly, but I wanted to keep it simple


-- SYNTAX

-- In the (untyped) While Language we have Naturals and Booleans
-- We can perform operations both on β (e.g. +, β€) and on πΉ (e.g. &, Β¬).
-- We have the if_then_else  and while_repeat flow control statements
-- Programs in While language may not terminate (while true repeat skip)
-- Variables are defined by the "location" (π) terms
-- Each location is associated with stores an Integer
-- Locations can be
--      β read:     ! lβ
--      β written:  lβ β (Eβ 3)


-- Auxiliary data
data πΉ : Set where
    true  : πΉ
    false : πΉ

infix 30 β 
data β : Set where
    zero    : β
    succ    : β β β

infixl 7 _Γ_
data _Γ_ (A B : Set) : Set where
  <_,_> : A -> B -> A Γ B

fst : {A B : Set} -> A Γ B -> A
fst < x , y > = x

snd : {A B : Set} -> A Γ B -> B
snd < x , y > = y

infixl 6 _+_
_+_ : β β β β β
zero   + m = m
succ k + m = succ (k + m)



infixl 5 _β€_
_β€_ : β β β β πΉ
zero  β€   zero     = true
zero β€    (succ m) = true
(succ n) β€ zero     = false
(succ n) β€ (succ m) =  n β€ m


infixr 5 List
data List (A : Set) : Set where
    []      : List A
    _β·_     : A β List AΒ β List A

data β₯ : Set where

data Maybe (A : Set) : Set where
    Nothing : Maybe A
    Just    : A β Maybe A


_β‘β_ : πΉ β πΉ β πΉ
true β‘β true = true
true β‘β false = false
false β‘β true = false
false β‘β false = true


Β¬_ : πΉ β πΉ
Β¬ true  = true
Β¬ false = true

_&_ : πΉ β πΉ β πΉ
true & true = true
true & false = false
false & true = false
false & false = false


-- While language Semantics

-- locations
data π : Set where
    first : π
    there : π β π



infixl 5 Expr
data Expr : (A : Set) β Set where
    Eβ                  : β β Expr β
    EπΉ                  : πΉ β Expr πΉ
    Eif_then_else_      : {A : Set} β Expr πΉ β Expr A β Expr A β Expr A
    Ewhile_repeat_      : {A : Set} β Expr πΉ β Expr A β Expr A
    skip                : Expr β₯
    _β_                 : π β Expr β β Expr β
    !_                  : π β Expr β
    _+β_                : Expr β β Expr β β Expr β
    _β€β_                : Expr β β Expr β β Expr πΉ
    _,_                 : {A : Set} β Expr A β Expr A β Expr A
    _β‘β_                : Expr πΉ β Expr πΉ β Expr πΉ
    Β¬β_                  : Expr πΉ β Expr πΉ
    _&β_                 : Expr πΉ β Expr πΉ β Expr πΉ
    

-- Some examples of expressions in While Language:
-- assignment: lβ = 0
_ : Expr β
_ = (there first) β (Eβ zero) 

-- if then else
_ : Expr β
_ = Eif (EπΉ true) then (! (there first)) else (Eβ (succ zero))

-- operations on locations
_ : Expr β
_ = ((there (there first)) β ((Eβ (succ zero)) +β (Eβ (succ (succ zero)))))  , ((! (there (there first))) +β (Eβ (succ zero)))

-- infinite cycle
_ : Expr β₯
_ = Ewhile (EπΉ true) repeat (skip)

-- SEMANTICS OF WHILE LANGUAGE

-- simple boolean equality function just for π
_β‘β_ : π β π β πΉ
first β‘β first = true
first β‘β there y = false
there x β‘β y = x β‘β y


-- extract the location content from the environment
extract : π β List (π Γ β) β Maybe β
extract l [] = Nothing
extract l (t β· env) with l β‘β (fst t)
... | true = Just (snd t)
... | false = extract l env

-- may not terminate (e.g. see the example term "infinite cycle" above) 
{-# NON_TERMINATING #-} 
execute : {A : Set} β Expr A β List (π Γ β) β (Maybe A Γ List (π Γ β))
-- βatural numbers
execute (Eβ x) env = < Just x , env >
-- πΉooleans
execute (EπΉ x) env = < Just x , env >
-- If then else
execute (Eif b then x else y) env with execute b env
... | < Just true , envβ > = execute x envβ
... | < Just false , envβ > = execute y envβ
... | < Nothing , envβ > = < Nothing , envβ >
-- While repeat
execute (Ewhile b repeat x) env with execute b env
... | < Just true , envβ > = execute (Ewhile b repeat x) (snd (execute x envβ))
... | < Just false , envβ > = < Nothing , envβ >
... | < Nothing , envβ > = < Nothing , envβ >
-- skip
execute skip env = < Nothing , env >
-- Assignment to location
execute (l β x) env with execute x env
... | < Just n , envβ > = < Just n , (< l , n > β· env ) >
... | < Nothing , envβ > = < Nothing , env >
-- Read a location
execute (! x) env with extract x env
... | y = < y , env >
-- Sum
execute (x +β y) env with execute x env
... | < Nothing , envβ > = <Β Nothing , envβ >
... | < Just xβ , envβ > with execute y envβ
... | < Just yβ , envβ > = <Β Just (xβ + yβ) , envβ >
... | < Nothing , envβ > = <Β Nothing , envβ >
-- β€ relation
execute (x β€β y) env with execute x env
... | < Nothing , envβ > = <Β Nothing , envβ >
... | < Just xβ , envβ > with execute y envβ
... | < Just yβ , envβ > = <Β Just (xβ β€ yβ) , envβ >
... | < Nothing , envβ > = <Β Nothing , envβ >
-- Concatenate
execute (x , y) env with execute x env
... | < xβ , envβ > = execute y envβ

execute (x β‘β y) env with execute x env
... | < Nothing , envβ > = < Nothing , envβ  >
... | < Just xβ , envβ > with execute y envβ
... | < Nothing , envβ > = < Nothing  , envβ  >
... | < Just yβ , envβ > = < Just (xβ β‘β yβ)  , envβ  >


execute (Β¬β x) env with execute x env
... | < Just xβ , envβ > = < Just (Β¬ xβ) , envβ >
... | < Nothing , envβ > = < Nothing , envβ >


execute (x &β y) env with execute x env
... | < Nothing , envβ > = < Nothing , envβ  >
... | < Just xβ , envβ > with execute y envβ
... | < Nothing , envβ > = < Nothing  , envβ  >
... | < Just yβ , envβ > = < Just (xβ & yβ)  , envβ  >




-- TESTING THE PROGRAM

expβ : Expr β
expβ = Eif (EπΉ true) then (! (there first)) else (Eβ (succ zero))

resβ = execute expβ []

