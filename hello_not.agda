data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
m + zero = m
m + succ(n) = succ(m + n)

_*_ : ℕ → ℕ → ℕ
m * zero = zero
m * succ(n) = m + (m * n)

two = succ(succ zero)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

doubling : (m : ℕ) → (m * two) ≡ (m + m)
-- somewhat surprisingly, this is enough:
doubling m = refl
-- this is because:
-- m * two = m + (m * succ(zero)) = m + (m + m * zero)
--         = m + (m + zero) = m + m

data ⊥ : Set where

¬_ : Set -> Set
¬ A = A → ⊥

obvious : (n : ℕ) → ¬ (n ≡ succ(n))
obvious n = λ ()

