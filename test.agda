data Boole : Set where
  true : Boole
  false : Boole

_&&_ : Boole → Boole → Boole
true && y = y
false && y = false

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

ttt : true && true ≡ true
ttt = refl

comm&& : ∀ (b b′ : Boole) → b && b′ ≡ b′ && b 
comm&& true true = refl
comm&& true false = refl
comm&& false true = refl
comm&& false false = refl

false&& : ∀ (b : Boole) → b && false ≡ false
false&& true = refl
false&& false = refl

tff : true && false ≡ false
-- tff = refl
-- tff = false&& true
tff = false&& false

data Nat : Set where
  zero : Nat
  1+ : Nat -> Nat

-- C-cC-a with "-l" "-s 8" in the hole
myNat : Nat
myNat = 1+ (1+ (1+ (1+ (1+ (1+ (1+ (1+ zero)))))))



