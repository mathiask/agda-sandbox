-- 20200915 Mathias Kegelmann

data Boole : Set where
  true : Boole
  false : Boole

not : Boole → Boole
not true = false
not false = true

-- not true

-- and : Boole → Boole → Boole
-- and true y = y
-- and false y = false

_&&_ : Boole → Boole → Boole
true && y = y
false && y = false

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

-- Aside: Function types are also sets
_ : Set
_ = Nat → Nat


_+_ : Nat → Nat → Nat
zero + y = y
succ x + y = succ (x + y)

two three : Nat
two = succ (succ zero)          -- {-s 2}
three = succ (succ (succ zero)) -- {-s 3}

-- two + three

five = two + three

-- ============================================================

-- This is needed in several spots in both branches,
-- introduce when needed

data _==_ (x : Nat) : Nat → Set where
  refl : x == x

infix 4 _==_

-- We could also compare this intentional equality to an
-- inductively defined equality.

-- Examples:
_ : two + two == succ (succ (succ (succ zero)))
_ = refl

-- ============================================================

-- Level 2
-- introduce when needed

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

record _~=~_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : (x : A) → from (to x) ≡ x
    to∘from : (y : B) → to (from y) ≡ y


-------------------- Math/Logic branch

data _<_ : Nat → Nat → Set where
  o< : (y : Nat) →  zero < succ y
  s< : (x y : Nat) → x < y → succ x < succ y

infix 4 _<_

_ : succ zero < three
_ = s< zero (succ (succ zero)) (o< (succ zero)) -- C-a

data TotallyOrdered (x y : Nat) : Set where
  x<y : x < y → TotallyOrdered x y
  x=y : x == y → TotallyOrdered x y
  x>y : y < x → TotallyOrdered x y

compare : (x y : Nat) → TotallyOrdered x y
compare zero zero = x=y refl
compare zero (succ y) = x<y (o< y)
compare (succ x) zero = x>y (o< x)
compare (succ x) (succ y) with compare x y
... | x<y xy = x<y (s< x y xy)
... | x=y refl = x=y refl
... | x>y yx = x>y (s< y x yx)


data False : Set where

¬_ : Set → Set
¬ A = A → False

_ : ¬(two + two == five)
_ = λ () -- C-a

not-less : ¬ (two < succ zero)
not-less (s< .(succ zero) .zero ())


data Decidable (A : Set) : Set where
  yes : A → Decidable A
  no : ¬ A → Decidable A

-- BEGIN Introduce at (1)
¬x<x : (x : Nat) → ¬ (x < x)
¬x<x (succ x) (s< x x xx) = ¬x<x x xx

-- (2)
<-not-sym : (x y : Nat) → x < y → ¬(y < x)
<-not-sym .(succ x) .(succ y) (s< x y xy) (s< .y .x yx) = <-not-sym x y xy yx
-- END

decide< : (x y : Nat) → Decidable (x < y)
decide< x y with compare x y
... | x<y xy = yes xy
-- here (1)
... | x=y refl = no (¬x<x x)
-- here (2)
... | x>y yx = no (<-not-sym y x yx)

-- -------------------- Level 2 --------------------

data _≤_ : Nat → Nat → Set where
  o≤ : (y : Nat) →  zero ≤ y
  s≤ : (x y : Nat) → x ≤ y → succ x ≤ succ y

-- (10)
refl≤ : (x : Nat) → x ≤ x
refl≤ zero = o≤ zero
refl≤ (succ x) = s≤ x x (refl≤ x)

data _⊎_ (A B : Set) : Set where
  left : A → A ⊎ B
  right : B → A ⊎ B

<≤ : (x y : Nat) → ((x < y) ⊎ (x == y)) ~=~ (x ≤ y)
<≤ x y = record {
  to = myto;
  from = myfrom ;
  from∘to = ft ;
  to∘from = tf} where
    myto : {x y : Nat} → ((x < y) ⊎ (x == y)) → (x ≤ y)
    myto (left (o< y)) = o≤ (succ y)
    myto (left (s< x y xy)) = s≤ x y (myto (left xy))
    -- (10)
    myto {x} (right refl) = refl≤ x
    myfrom : {x y : Nat} → (x ≤ y) → ((x < y) ⊎ (x == y))
    myfrom (o≤ zero) = right refl
    myfrom (o≤ (succ y)) = left (o< y)
    myfrom (s≤ x y xy) with myfrom {x} {y} xy
    ... | left a = left (s< x y a)
    ... | right refl = right refl
    ft : {x y : Nat} (xy : (x < y) ⊎ (x == y)) → myfrom(myto xy) ≡ xy
    ft (left (o< _)) = refl
    ft (left (s< x y a)) rewrite (ft (left a)) = refl
    ft {zero} {.zero} (right refl) = refl
    ft {succ x} {succ x} (right refl) rewrite (ft (right refl)) = {!!}
    tf : {x y : Nat} (xy : x ≤ y) → myto(myfrom xy) ≡ xy
    tf xy = {!!}

-- ==================== CS branch ====================

data NList : Set where
  nil : NList
  cons : Nat → NList → NList

-- _ : NList
-- _ = {!-l!}

append : NList → NList → NList
append nil l2 = l2
append (cons x l1) l2 = cons x (append l1 l2)

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

-- -------------------- Level 2 --------------------
