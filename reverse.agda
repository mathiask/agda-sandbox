data Nat : Set where
  zero : Nat
  suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 40 _::_

_++_ : {A : Set} → List A → List A → List A
[] ++ l2 = l2
(x :: l1) ++ l2 = x :: (l1 ++ l2)

infix 30 _++_

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x :: l) = reverse l ++  x :: []

frev : {A : Set} → List A → List A → List A
frev [] a = a
frev (x :: l) a = frev l (x :: a)

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

infixr 10 _≡_

-- Step (0)
-- postulate 
--   frev-is-rev-append : {A : Set} → (acc : List A) 
--     → (l : List A) → frev l acc ≡ reverse l ++ acc

-- Step (4)
cong : {A B : Set} → (f : A → B) → {a1 a2 : A} → a1 ≡ a2 → f a1 ≡ f a2
cong f refl = refl

-- Step (3)
assoc++ : {A : Set} → (l1 l2 l3  : List A) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
assoc++ [] l2 l3 = refl
-- (4)
assoc++ (x :: l1) l2 l3 = cong (λ l → x :: l) (assoc++ l1 l2 l3)

{-# BUILTIN EQUALITY _≡_ #-} 

frev-is-rev-append : {A : Set}
  → (acc : List A) 
  → (l : List A)
  → frev l acc ≡ (reverse l) ++ acc
-- Step (2)
frev-is-rev-append acc [] = refl
-- (3)
frev-is-rev-append acc (x :: l) rewrite assoc++ (reverse l) (x :: []) acc
  = frev-is-rev-append (x :: acc) l

-- Step (1)
frev-reverses : {A : Set}→ (l : List A) → frev l [] ≡ reverse l
frev-reverses [] = refl
frev-reverses (x :: l) = frev-is-rev-append (x :: []) l
-- frev-is-rev-append [x] l = 
-- frev l [x] ≡ (append (reverse l) [x])
-- frev (x :: l) ≡ reverse (x :: l)
