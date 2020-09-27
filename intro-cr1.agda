-- 20200915 Mathias Kegelmann

data Boole : Set where
  true : Boole
  false : Boole

not : Boole → Boole
not true = false
not false = true

-- and : Boole → Boole → Boole
-- and true y = y
-- and false y = false

_&&_ : Boole → Boole → Boole
true && y = y
false && y = false

-- not true

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

_+_ : Nat → Nat → Nat
zero + y = y
succ x + y = succ (x + y)

two three : Nat
two = succ (succ zero)          -- {-s 2}
three = succ (succ (succ zero)) -- {-s 3}

-- two + three

-------------------- Math/Logic branch

data _≤_ : Nat → Nat → Set where
  o≤ : (y : Nat) →  zero ≤ y
  s≤ : (x y : Nat) → x ≤ y → succ x ≤ succ y

infix 4 _≤_

_ : succ zero ≤ three
_ = s≤ zero (succ (succ zero)) (o≤ (succ (succ zero))) -- C-a

data False : Set where

¬_ : Set → Set
¬ A = A → False

-- Function types are also sets
_ : Set
_ = Nat → Nat

not-less : ¬ (two ≤ succ zero)
not-less (s≤ .(succ zero) .zero ())

data TotallyOrdered (x y : Nat) : Set where
  x<y : x ≤ y → TotallyOrdered x y
  x>y : y ≤ x → TotallyOrdered x y

compare : (x y : Nat) → TotallyOrdered x y
-- compare x y = ?
compare zero y = x<y (o≤ y)
compare (succ x) zero = x>y (o≤ (succ x))
compare (succ x) (succ y) with compare x y
... | x<y xy = x<y (s≤ x y xy)
... | x>y yx = x>y (s≤ y x yx)

data Decidable (A : Set) : Set where
  yes : A → Decidable A
  no : ¬ A → Decidable A

-- BEGIN Introduce at (1)
s¬≤ : (x y : Nat) → ¬(x ≤ y) → ¬(succ x ≤ succ y)
s¬≤ x y ¬x≤y sx≤sy = s¬≤ x y ¬x≤y sx≤sy
-- END

decide≤ : (x y : Nat) → Decidable (x ≤ y)
decide≤ zero y = yes (o≤ y)
decide≤ (succ x) zero = no (λ ())
decide≤ (succ x) (succ y) with decide≤ x y
... | yes x≤y = yes (s≤ x y x≤y)
{- here (1) -}
... | no ¬x≤y = no (s¬≤ x y ¬x≤y)


-------------------- CS branch

data NList : Set where
  nil : NList
  cons : Nat → NList → NList

-- _ : NList
-- _ = {!-l!}

append : NList → NList → NList
append nil l2 = l2
append (cons x l1) l2 = cons x (append l1 l2)

data _==_ (x : Nat) : Nat → Set where
  refl : x == x

infix 4 _==_

length : NList → Nat
length nil = zero
length (cons x l) = succ (length l)

-- BEGIN Introduce at (2)
cong : (x y : Nat) → x == y → succ x == succ y
cong x .x refl = refl

icong : {x y : Nat} → x == y → succ x == succ y
icong {x} {.x} refl = refl
-- END

append→add : ∀ (l1 l2 : NList) → length (append l1 l2) == (length l1) + (length l2)
append→add nil l2 = refl
{- here (2) -}
append→add (cons x l1) l2 = cong (length (append l1 l2)) (length l1 + length l2) (append→add l1 l2)

-- polymorphism is free

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A
