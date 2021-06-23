-- CONSTRUCTIVE ZERMELO--FRAENKEL in AGDA

-- Goal: talk about sets in Agda
-- more specifically: want to have an Agda datatype V of sets
-- emptySet : V
-- N : V
-- ...

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- "SETS AS TREES"

data V : Set₁ where
  sup : {I : Set} → (I → V) → V
{-
  empty        : V
  union        : V → V → V
  intersection : V → V → V
  N            : V
  ...
-}

emptySet : V
emptySet = sup {⊥} (λ ())
  where
  data ⊥ : Set where
-- as a tree: *

-- pair x y = "{x,y}" (a set which has typically two elements)
pair : V → V → V
pair x y = sup {𝟚} λ { left → x ; right → y }
  where
  data 𝟚 : Set where
    left  : 𝟚
    right : 𝟚
-- as tree:        *
--                / \
--               x   y

-- singleton x = "{x}" (a set which contains precisely one element)
singleton : V → V
-- singleton x = pair x x
singleton x = sup {𝟙} λ { * → x }
  where
  data 𝟙 : Set where
    * : 𝟙
-- as a tree:    *
--               |
--               x

-- natural numbers in set theory:
-- 0 := ∅ = {}
-- 1 := { 0 } = { {} }
-- 2 := { 0, 1 } = { {}, {{}} }
-- 3 := { 0, 1, 2 } = { {}, {{}}, {{},{{}}} }
-- succ(n) = n ∪ {n}

_∪_ : V → V → V
_∪_ = {!!}

-- next(x) = x ∪ {x}
next : V → V
next x = x ∪ singleton x

fromℕ : ℕ → V
fromℕ zero    = emptySet
fromℕ (suc n) = next (fromℕ n)

N : V
N = sup {ℕ} fromℕ
-- as a tree:      *
--               //  \  \
--             0  1   2  3  4 ...          