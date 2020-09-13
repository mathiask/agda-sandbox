-- 20200430 Mathias Kegelmann
-- 20200903 - added subtraction and division

-- Some preliminaries?
-- to explain
-- * types = Set
-- * pattern matching
-- * inductive/recursive definitions

-- ========== Arithmetic ==========

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
m + zero = m
m + succ(n) = succ(m + n)

-- Expression to evaluate (C-c C-n "normal form", or C-u C-u C-c C-n)

_*_ : ℕ → ℕ → ℕ
m * zero = zero
m * succ(n) = m + (m * n)

two = succ(succ zero)

-- Evaluate (C-c C-n): two * succ(two)


-- ========== Equality ==========

-- Or as a theorem (C-c C-f, C-c C-r, or C-c C-a):

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

two_times_three_is_six : two * succ(two) ≡ succ(succ(succ(succ(succ(succ(zero))))))
two_times_three_is_six = refl

-- How about inductive equality

data _≡ₙ_ : ℕ → ℕ → Set where
  eq-base : zero ≡ₙ zero
  eq-ind : {n : ℕ} → n ≡ₙ n → succ(n) ≡ₙ succ(n)
infix 4 _≡ₙ_

two_times_three_is_six_ind : two * succ(two) ≡ₙ succ(succ(succ(succ(succ(succ(zero))))))
two_times_three_is_six_ind = eq-ind (eq-ind (eq-ind (eq-ind (eq-ind (eq-ind eq-base)))))

-- They are the same equality (C-c C-c, C-c C-r, C-c C-a)::

intensional→inductive : (m n : ℕ) → m ≡ n → m ≡ₙ n
intensional→inductive zero _ refl = eq-base
intensional→inductive (succ m) _ refl = eq-ind (intensional→inductive _ m refl)

-- harder
inductive→intensional : ∀ (m n : ℕ) → m ≡ₙ n → m ≡ n
inductive→intensional zero _ eq-base = refl
inductive→intensional (succ _) (succ _) (eq-ind _) = refl

two_times_three_is_six_ind2 : two * succ(two) ≡ₙ succ(succ(succ(succ(succ(succ(zero))))))
two_times_three_is_six_ind2 = intensional→inductive _ _ refl

-- ========== Odd and Even ==========

data evenᵢ : ℕ → Set where
  e0 : evenᵢ zero
  e+2 : {n : ℕ} → evenᵢ n → evenᵢ (succ(succ n))

data oddᵢ : ℕ → Set where
  o1 : oddᵢ (succ zero)
  o+2 : {n : ℕ} → oddᵢ n → oddᵢ (succ(succ n))

even→odd : {n : ℕ} → evenᵢ n → oddᵢ (succ n)
even→odd {zero} _ = o1
even→odd {succ (succ _)} (e+2 en) = o+2 (even→odd en)

data ⊥ : Set where
  -- no clauses

¬_ : Set → Set
¬ A = A → ⊥

-- C-c C-a
0notodd : ¬ (oddᵢ zero)
0notodd = λ ()

odd→even :  {n : ℕ} → oddᵢ (succ n) → evenᵢ n
odd→even {zero} _ = e0
odd→even {succ (succ _)} (o+2 osn) = e+2 (odd→even osn)

e+2' : {n : ℕ} → evenᵢ (succ (succ n)) → evenᵢ n
e+2' (e+2 essn) = essn

o+2' : {n : ℕ} → oddᵢ (succ (succ n)) → oddᵢ n
o+2' (o+2 ossn) = ossn

even→odd' : {n : ℕ} → evenᵢ (succ n) → oddᵢ n
even→odd' esn = o+2' (even→odd esn)

odd→even' :  ∀ {n : ℕ} → oddᵢ n → evenᵢ (succ n)
odd→even' on =  odd→even (o+2 on)

-- Every number is either odd or even.
-- What does 'or' mean?

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

-- uses "with"
even-or-odd : ∀ (n : ℕ) → evenᵢ n ⊎ oddᵢ n
even-or-odd zero = inj₁ e0
even-or-odd (succ n) with (even-or-odd n)
... | inj₁ en = inj₂ (even→odd en)
... | inj₂ on = inj₁ (odd→even' on)

-- implicit currying to avoid "and"
not-even-and-odd : ∀ (n : ℕ) → evenᵢ n → oddᵢ n → ⊥
not-even-and-odd (succ (succ n)) (e+2 en) (o+2 on) = not-even-and-odd n en on


-- Now let's try the usual, arithmetic approach:
-- even is defined by divisibility by two:
-- The challenge is the exstential qualtification
-- ∃ [m:ℕ] n ≡ m + m

data ∃ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → ∃ A B

evenₐ : ℕ → Set
evenₐ n = ∃ ℕ (λ m → n ≡ m + m)

-- unfortunately, here we'd need equational reasoning

symm : ∀ {A : Set} (a₁ a₂ : A) → a₁ ≡ a₂ → a₂ ≡ a₁
symm _ _ refl = refl

trans : ∀ {A : Set} (a₁ a₂ a₃ : A) → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃
trans _ _ _ refl refl = refl

cong : ∀ {A B : Set} (a₁ a₂ : A) (f : A → B) → (a₁ ≡ a₂) → f a₁ ≡ f a₂
cong _ _ _ refl = refl

subst : ∀ {A : Set} (a₁ a₂ : A) (P : A → Set) → (a₁ ≡ a₂) → (P a₁) → (P a₂)
subst _ _ _ refl Pa = Pa

smn : ∀ (m₁ m₂ : ℕ) → succ(m₁ + m₂) ≡ succ m₁ + m₂
smn _ zero = refl
smn m₁ (succ m₂) = cong (m₁ + succ m₂) (succ m₁ + m₂) succ (smn m₁ m₂) 

n+n-even : ∀ (n : ℕ) → evenᵢ (n + n)
n+n-even zero = e0
n+n-even (succ n) = subst (succ(succ(n + n))) (succ(succ n + n))
                    evenᵢ
                    (cong (succ (n + n)) (succ n + n) succ (smn n n))
                    (e+2 (n+n-even n))

even-a→i : ∀ (n : ℕ) → evenₐ n → evenᵢ n
even-a→i zero _ = e0
even-a→i (succ n) ⟨ m , p ⟩ =
  subst (m + m) (succ n) evenᵢ (symm (succ n) (m + m) p) (n+n-even m)

even-i→a : ∀ (n : ℕ) → evenᵢ n → evenₐ n
even-i→a zero _ = ⟨ zero , refl ⟩
even-i→a (succ (succ n)) (e+2 en) with (even-i→a n en)
... | ⟨ m , n=m+m ⟩ = ⟨ (succ m) , (cong (succ n) (succ m + m) succ
                                   (trans (succ n) (succ (m + m)) (succ m + m)
                                     (cong n (m + m) succ n=m+m)
                                     (smn m m))) ⟩

-- ========== Subtraction ==========

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ _ = zero
(succ m) ∸ (succ n) = m ∸ n

+-inv : (m n : ℕ) → (m + n) ∸ n ≡ m
+-inv _ zero = refl
+-inv zero (succ n) = +-inv zero n
+-inv (succ m) (succ n) = +-inv (succ m) n


data _≤_ : ℕ → ℕ → Set where
  zero≤ : (n : ℕ) → zero ≤ n
  succ≤ : {m n : ℕ} → m ≤ n →  (succ m) ≤ (succ n)

-+inv : (m n : ℕ) → m ≤ n → (n ∸ m) + m ≡ n
-+inv zero zero (zero≤ .zero) = refl
-+inv zero (succ n) (zero≤ .(succ n)) = refl
-+inv (succ m) (succ n) (succ≤ m≦n) = cong ((n ∸ m) + m) n succ (-+inv m n m≦n)

/-helper : ℕ → ℕ → ℕ → ℕ → ℕ
/-helper k _ zero _ = k
/-helper k n (succ m) zero = /-helper (succ k) n m n
/-helper k n (succ m) (succ o) = /-helper k n m o

data Maybe_ : (A : Set) → Set where
  just : {A : Set} → A → Maybe A
  none : {A : Set} → Maybe A

_/_ : ℕ → ℕ → Maybe ℕ
m / zero = none
m / succ n = just (/-helper zero n m n)


-- To show interesting properties of / we need more "basic" arithmetic.

0+ : (n : ℕ) → zero + n ≡ n
0+ zero = refl
0+ (succ n) = cong (zero + n) n succ (0+ n)

1+ : (n : ℕ) → (succ zero) + n ≡ succ n
1+ zero = refl
1+ (succ n) = cong (succ zero + n) (succ n) succ (1+ n)

comm+ : (x y : ℕ) → x + y ≡ y + x
comm+ zero zero = refl
comm+ zero (succ y) = cong (zero + y) y succ (0+ y)
comm+ (succ x) zero = cong x (zero + x) succ (symm (zero + x) x (0+ x))
comm+ (succ x) (succ y) = cong {!!} {!!} succ (comm+ {!!} {!!})

0* : (n : ℕ) → zero * n ≡ zero
0* zero = refl
0* (succ n) = trans (zero + (zero * n)) (zero * n) zero (0+ (zero * n)) (0* n)

1* : (n : ℕ) → (succ zero) * n ≡ n
1* zero = refl
1* (succ n) = trans (succ zero + (succ zero * n))
                    (succ zero + n)
                    (succ n)
                    (trans (succ zero + (succ zero * n))
                           (succ zero + n)
                           (succ zero + n)
                           (cong (succ zero * n)
                                 n
                                 (λ x → succ zero + x)
                                 (1* n))
                           refl)
                    (1+ n)

------------------------------

*/ : (m n : ℕ) → (m * (succ n)) / (succ n) ≡ just m
*/ zero n = cong (/-helper zero n (zero + (zero * n)) n) zero just h1 where
  h1 : /-helper zero n (zero + (zero * n)) n ≡ zero
  h1 = trans (/-helper zero n (zero + (zero * n)) n)
             (/-helper zero n zero n)
             zero
             (cong ((zero + (zero * n)))
                   zero
                   (λ x → /-helper zero n x n)
                   (cong (zero * n) zero (λ x → zero + x) (0* n)))
             refl
*/ (succ m) zero = {!!}
*/ (succ m) (succ n) = {!!}
