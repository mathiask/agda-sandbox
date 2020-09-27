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

<→≤ : (x y : Nat) → x < y → x ≤ y
<→≤ zero (succ y) (o< y) = o≤ (succ y)
<→≤ (succ x) (succ y) (s< x y xy) = s≤ x y (<→≤ x y xy)

=→≤ : (x y : Nat) → x == y → x ≤ y
=→≤ x x refl = refl≤ x

data _⊎_ (A B : Set) : Set where
  left : A → A ⊎ B
  right : B → A ⊎ B

≤→<= : (x y : Nat) → x ≤ y → (x < y) ⊎ (x == y)
≤→<= zero zero (o≤ zero) = right refl
≤→<= zero (succ y) (o≤ (succ y)) = left (o< y)
≤→<= (succ x) (succ y) (s≤ x y xy) with ≤→<= x y xy
... | left l = left (s< x y l)
... | right refl = right refl

<=→≤ : (x y : Nat) → (x < y) ⊎ (x == y) → x ≤ y 
<=→≤ x y (left xy) = <→≤ x y xy
<=→≤ x y (right refl) = =→≤ x x refl

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

data Unit : Set where
  ∗ : Unit

fromNat : Nat → List Unit
fromNat zero = nil
fromNat (succ n) = cons ∗ (fromNat n)

toNat : List Unit → Nat
toNat nil = zero
toNat (cons ∗ l) = succ (toNat l)

isoOnNat : (n : Nat) → toNat (fromNat n) ≡ n
isoOnNat zero = refl
isoOnNat (succ n) rewrite isoOnNat n = refl

isoOnList* : (l : List Unit) → fromNat(toNat l) ≡ l
isoOnList* nil = refl
isoOnList* (cons ∗ l) rewrite isoOnList* l = refl

0isNil : fromNat zero ≡ nil
0isNil = refl

nilIs0 : toNat nil ≡ zero
nilIs0 = refl

_++_ : {A : Set} → List A → List A → List A
nil ++ l2 = l2
cons x l1 ++ l2 = cons x (l1 ++ l2)

addIsAppend : (x y : Nat) → fromNat (x + y) ≡ (fromNat x) ++ (fromNat y)
addIsAppend zero y = refl
addIsAppend (succ x) y rewrite addIsAppend x y = refl

appendIsAdd : (l1 l2 : List Unit) → toNat (l1 ++ l2) ≡ (toNat l1) + (toNat l2)
appendIsAdd nil l2 = refl
appendIsAdd (cons ∗ l1) l2 rewrite appendIsAdd l1 l2 = refl

-- -------------------- Level 3 --------------------

_*_ : Nat → Nat → Nat
zero * y = zero
succ x * y = y + (x * y)

-- three * five

one = succ zero

0*n : (n : Nat) → zero * n ≡ zero
0*n n = refl

n+0 : (n : Nat) → n + zero ≡ n
n+0 zero = refl
n+0 (succ n) rewrite n+0 n = refl

1neutral : (n : Nat) → one * n ≡ n
1neutral zero = refl
1neutral (succ n) rewrite 0*n (succ n) | n+0 n = refl

data _×_  (A B : Set) : Set where
   _,_ : A → B → A × B


map : {A B : Set} → (f : A → B) → List A → List B
map f nil = nil
map f (cons x l) = cons (f x) (map f l)


_*L_ : {A B : Set} → List A → List B → List (A × B)
nil *L l2 = nil
_*L_ {A} {B} (cons x l1) l2 = map (_,_ x) l2  ++ (l1 *L l2)

1to1*1 : Unit → Unit × Unit
1to1*1 ∗ = ∗ , ∗

1*1to1 : Unit × Unit → Unit
1*1to1 (∗ , ∗) = ∗

iso1 : (u : Unit) → 1*1to1 (1to1*1 u) ≡ u
iso1 ∗ = refl

iso11 : (uu : Unit × Unit) → 1to1*1 (1*1to1 uu) ≡ uu
iso11 (∗ , ∗) = refl


1is* : fromNat one ≡ cons ∗ nil
1is* = refl

-- just to show that we can also reason using iso
*is1 : toNat (cons ∗ nil) ≡ one
-- *is1 = refl
*is1 rewrite 1is* = refl

mapAppend : {A B : Set} → (f : A → B) → (l1 l2 : List A) → map f (l1 ++ l2) ≡ (map f l1) ++ (map f l2)
mapAppend f nil l2 = refl
mapAppend f (cons x l1) l2 rewrite mapAppend f l1 l2 = refl

1*and1to1*1 : (l : List Unit) → map (_,_ ∗) l ≡ map 1to1*1 l
1*and1to1*1 nil = refl
1*and1to1*1 (cons ∗ l) rewrite 1*and1to1*1 l = refl

mapIso : (l : List Unit) → map 1*1to1 (map 1to1*1 l) ≡ l
mapIso nil = refl
mapIso (cons ∗ l) rewrite mapIso l = refl

timesIsProduct : (x y : Nat) → fromNat (x * y) ≡ map 1*1to1 ((fromNat x) *L (fromNat y))
timesIsProduct zero y = refl
timesIsProduct (succ x) y rewrite addIsAppend y (x * y)
  | mapAppend 1*1to1 (map (_,_ ∗) (fromNat y)) (fromNat x *L fromNat y)
  | timesIsProduct x y
  | 1*and1to1*1 (fromNat y)
  | mapIso (fromNat y)
  = refl

-- ... which implies ...

comm≡ : {A : Set} {x y : A} → x ≡ y → y ≡ x
comm≡ {x=x} {y=x} refl = refl

productIsTimes : (l1 l2 : List Unit) → toNat (map 1*1to1 (l1 *L l2)) ≡ (toNat l1) * (toNat l2)
productIsTimes l1 l2 rewrite comm≡ (isoOnList* l1) | comm≡ (isoOnList* l2)
  | comm≡ (timesIsProduct (toNat l1) (toNat l2))
  | isoOnNat (toNat l1 * toNat l2) | isoOnNat (toNat l1) | isoOnNat (toNat l2)
  = refl
