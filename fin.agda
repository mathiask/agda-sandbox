{-# OPTIONS --prop #-}

data False : Prop where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc : {n : Nat} → Fin n → Fin (suc n)

fin0empty : (x : Fin zero) → False
fin0empty ()

0infin1 : Fin (suc zero)
0infin1 = zero

0infin2 : Fin (suc (suc zero))
0infin2 = zero

1infin2 : Fin (suc (suc zero))
1infin2 = suc zero

finInNat : {n : Nat} → Fin n → Nat
finInNat zero = zero
finInNat (suc x) = suc (finInNat x)

data _<_ : Nat → Nat → Set where
  0< : (n : Nat) → zero < (suc n)
  s< : {m n : Nat} → m < n → (suc m) < (suc n)

n<sn : (n : Nat) → n < suc n
n<sn zero = 0< zero
n<sn (suc n) = s< (n<sn n)

natInFin : (x n : Nat) → x < n → Fin n
natInFin zero (suc n) _ = zero
natInFin (suc x) (suc n) (s< x<n) = suc (natInFin x n x<n)

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

iso1 : (n : Nat) → finInNat (natInFin n (suc n) (n<sn n)) ≡ n
iso1 zero = refl
iso1 (suc x) = cong suc (iso1 x)

fin< : (n : Nat) → (x : Fin n) → finInNat {n} x < n
fin< (suc n) zero = 0< n
fin< (suc n) (suc x) = s< (fin< n x)

iso2 : {n : Nat} → (x : Fin n) → natInFin (finInNat {n} x) n (fin< n x) ≡ x
iso2 zero = refl
iso2 {suc n} (suc x) = cong suc (iso2 x)
