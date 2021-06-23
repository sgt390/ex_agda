data 𝔹 : Set where
    true  : 𝔹
    false : 𝔹

data ℕ : Set where
    zero    : ℕ
    succ    : ℕ → ℕ


data List (A : Set) : Set where
    []      : List A
    _∷_     : A → List A → List A

data Tuple (A : Set) : Set where
    empty   : Tuple A
    _,_     : A → A → Tuple A
 

data Expr : (A : Set) → Set where
    Eℕ      : ℕ → (Expr ℕ)
    E𝔹      : 𝔹 → (Expr 𝔹)
    Eλ      : (List ℕ) → Expr ℕ → Expr ℕ
    EIf     : Expr 𝔹 → Expr ℕ → Expr ℕ → Expr ℕ
    EWhile  : Expr 𝔹 → Expr ℕ
    EVar    : List (Tuple ℕ) → Expr ℕ
    E+      : Expr ℕ → Expr ℕ → Expr ℕ
    E≤      : Expr ℕ → Expr ℕ → Expr 𝔹
    


_ : Expr ℕ
_ = ENum zero


_ : Expr ℕ
_ = EIf (EBool true) (EVar ((zero , succ zero) ∷ [])) (ENum (succ zero))


