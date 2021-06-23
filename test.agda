data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ


_+_ : ℕ → ℕ → ℕ
x + zero = x  
x + succ y = succ (x + y)

one : ℕ
one = succ zero

two : ℕ
two = succ (succ zero)