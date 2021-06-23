data 𝔹 : Set where
    true  : 𝔹
    false : 𝔹

data ℕ : Set where
    zero    : ℕ
    succ    : ℕ → ℕ


data List (A : Set) : Set where
    []      : List A
    _∷_     : A → List A → List A


data Expr : Set where
    Eℕ                  : ℕ → Expr
    E𝔹                  : 𝔹 → Expr
    EIf_then_else_      : Expr → Expr → Expr → Expr
    EWhile              : Expr → Expr → Expr
    E𝕃                  : ℕ → Expr
    skip                : Expr
    _≡_                 : Expr → Expr → Expr
    !_                  : Expr → Expr
    E+                  : Expr → Expr → Expr
    E≤                  : Expr → Expr → Expr
    _,_                 : Expr → Expr → Expr
    


_ : Expr
_ = Eℕ zero


_ : Expr
_ = EIf (E𝔹 true) then (E𝕃 (succ zero)) else (Eℕ (succ zero))


