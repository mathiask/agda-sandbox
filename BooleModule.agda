-- http://www.cse.chalmers.se/edu/year/2017/course/DAT140_Types/LectureNotes.pdf
-- [Peter Dybjer]
-- MK 20190821

module BooleModule where

data Boole : Set where
  true : Boole
  false : Boole

not : Boole → Boole
not true = false
not false = true

¬¬ : Boole → Boole
¬¬ b = not (not b)

if_then_else_ : {A : Set} → Boole → (x : A) → (y : A) → A
if true then x else y = x
if false then x else y = y

_&&_ : Boole → Boole → Boole
b && true = b
b && false = false

infixl 50 _&&_

_||_ : Boole → Boole → Boole
true || c = true
false || c = c

_⇒_ : Boole → Boole → Boole
true ⇒ c = c
false ⇒ c = true

_⇔_ : Boole → Boole → Boole
true ⇔ true = true
true ⇔ false = false
false ⇔ true = false
false ⇔ false = true

----------------------------------------------------------------------

module NatModule where 

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one = succ zero
two = succ one

_+_ : ℕ → ℕ → ℕ
m + zero = m
m + succ n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
m * zero = zero
m * succ n = m + (m * n)

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

_∸_ : ℕ → ℕ → ℕ
zero ∸ n = zero
m ∸ zero = m
succ m ∸ succ n = m ∸ n

_<_ : ℕ → ℕ → Boole
m < zero = false
zero < succ n = true
succ m < succ n = m < n

infixl 60 _+_ _∸_
infixl 70 _*_

_^_ : ℕ → ℕ → ℕ
m ^ zero = one
m ^ succ n = m * (m ^ n)

!_ : ℕ → ℕ
! zero = one
! succ m = (! m) * succ m

-- reverse binary numbers, i.e. x1 x1 x0 x1 nil = 11
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 bs) = x1 bs
inc (x1 bs) = x0 inc bs

from : Bin → ℕ
from nil = zero
from (x0 bs) = two * from bs
from (x1 bs) = one + two * from bs

to : ℕ → Bin
to zero = x0 nil
to (succ m) = inc (to m)

----------------------------------------------------------------------

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

onePlusOneIsTwo : one + one ≡ two
onePlusOneIsTwo = refl

doubleNegation : (b : Boole) → b ≡ b
doubleNegation true = refl
doubleNegation false = refl
-- or alternatively: doubleNegation b = refl (which now works)

sym : {A : Set } → (a a′ : A) → a ≡ a′ → a′ ≡ a
sym a .a refl = refl

trans : {A : Set} → {a₁ a₂ a₃ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃
trans refl refl = refl

subst : {A : Set} → {P : A → Set} → {a₁ a₂ : A} → a₁ ≡ a₂ → P a₁ → P a₂
subst refl q = q

cong : {A B : Set} → {a₁ a₂ : A} → (f : A → B) → a₁ ≡ a₂ → f a₁ ≡ f a₂
cong f refl = refl

associativity-plus : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
associativity-plus m n zero = refl
associativity-plus m n (succ p) = cong succ (associativity-plus m n p)

ℕind : {P : ℕ → Set}
  → P zero
  → ((m : ℕ) → P m → P (succ m))
  → (n : ℕ) → P n
ℕind base step zero = base
ℕind base step (succ n) = step n (ℕind base step n)

associativity-plus-ind : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
associativity-plus-ind m n =
  ℕind refl (λ _ → cong succ)

0-neutral-left : (m : ℕ) → 0 + m ≡ m
0-neutral-left = ℕind refl \_ → cong succ

0-neutral-right : (m : ℕ) → m + 0 ≡ m
0-neutral-right _ = refl

succ+right : (m n : ℕ) → m + succ n ≡ succ (m + n)
succ+right _ _ = refl

succ+left : (m n : ℕ) → succ m + n ≡ succ (m + n)
succ+left m =
  ℕind refl \_ → cong succ

commutativity-plus : (m n : ℕ) → m + n ≡ n + m
commutativity-plus m zero = sym (zero + m) m (0-neutral-left m)
commutativity-plus m (succ n) = sym (succ n + m) (succ(m + n))
  (trans (succ+left n m) (cong succ (commutativity-plus n m)))

----------------------------------------------------------------------

I : {A : Set} → A → A
I x = x

B : {A B C : Set} → (B → C) → (A → B) → A → C
B g f x = g (f x)

K : {A B : Set} → A → B → A
K x y = x

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S g f x = g x (f x)

data _&_ (A B : Set) : Set where
  <_,_> : A → B → A & B

fst& : {A B : Set} → A & B → A
fst& < x , y > = x

snd& : {A B : Set} → A & B → B
snd& < x , y > = y

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

case : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
case f g (inl x) = f x
case f g (inr y) = g y

comm-∨ : (A B : Set) → A ∨ B → B ∨ A
comm-∨ A B (inl a) = inr a
comm-∨ A B (inr b) = inl b

comm& : (A B : Set) → A & B → B & A
comm& A B < x , y > = < y , x >

data ⊤ : Set where
  <> : ⊤

data ⊥ : Set where
-- not inhabited

nocase : {C : Set} → ⊥ → C
nocase ()

-- optional explcit implication type with introduction rule
data _⊃_ (A B : Set) : Set where
  ⊃-intro : (A → B) → A ⊃ B

mp : {A B : Set} → A ⊃ B → A → B
mp (⊃-intro f) x = f x

¬ : Set → Set
¬ A = A → ⊥

inverse-dn : (A : Set) → A → ¬(¬ A)
inverse-dn A a = \f → f a

triple-neg : (A : Set) → ¬(¬(¬ A)) → ¬ A
triple-neg A f a = f (inverse-dn A a)

tndImpliesDn : (A : Set) → (A ∨ ¬ A) → ¬(¬ A) → A
tndImpliesDn A aona nna = case I (λ na → nocase (nna na)) aona

notNotTnd : (A : Set) → ¬(¬(A ∨ ¬ A))
notNotTnd A n = n (inr (λ a → n (inl a)))

dnImpliesTnd : ((X : Set) → (¬(¬ X) → X)) → (A : Set) → (A ∨ ¬ A)
dnImpliesTnd dn A = dn (A ∨ ¬ A) (notNotTnd A)

----------------------------------------------------------------------

data ∃ (A : Set) (P : A → Set) : Set where
  <_,_> : (a : A) → P a → ∃ A P

witness : {A : Set} {P : A → Set} → ∃ A P → A
witness < a , p > = a

proof : {A : Set} {P : A → Set} → (c : ∃ A P) → P (witness c)
proof < a , p > = p

∃elim : {A : Set} → {P : A → Set} → {Q : Set} → ((a : A) → P a → Q) → ∃ A P → Q
∃elim f < a , p > = f a p

data _×_ (A B : Set) : Set where
  <_,_> : A → B → A × B

fst : {A B : Set} → A × B → A
fst < a , b > = a

snd : {A B : Set} → A × B → B
snd < a , b > = b

uncurry : { A B C : Set } → (A → B → C) → A × B → C
uncurry f < a , b > = f a b

-- optional explicit universal quantification
data ∀′ (A : Set) (P : A → Set) : Set where
  ∀′-intro : ((x : A) → P x) → ∀′ A P

∀′-elim : {A : Set} {P : A → Set} → ∀′ A P → (a : A) → P a
∀′-elim (∀′-intro f) a = f a
