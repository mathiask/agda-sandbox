data Boole : Set where
  true : Boole
  false : Boole

not : Boole -> Boole
not true = false
not false = true

myBoole : Boole
myBoole = not true

and : Boole -> Boole -> Boole
and true y = y
and false y = false

data Nat : Set where
  zero : Nat
  1+ : Nat -> Nat

-- C-cC-a with "-l" "-s 8" in the hole

myNat : Nat
myNat = 1+ (1+ (1+ (1+ (1+ zero))))

{-# BUILTIN NATURAL Nat #-}

_<=_ : Nat -> Nat -> Boole
zero <= y = true
1+ x <= zero = false
1+ x <= 1+ y = x <= y

data List : Set where
  nil : List
  _::_ : Nat -> List -> List

infixr 5 _::_

myList : List
myList = 1 :: 2 :: nil

append : List -> List -> List
append nil l = l
append (x :: xs) l = x :: (append xs l)

data Tree : Set where
  leaf : Tree
  node : (p : Nat) -> (lt rt : Tree) -> Tree

toList : Tree -> List
toList leaf = nil
toList (node p lt rt) = append (toList lt) (p :: toList rt)

-- "proper" arrows

insert : Nat → Tree → Tree
insert n leaf = node n leaf leaf
insert n (node p lt rt) with n <= p
... | true = node p (insert n lt) rt
... | false = node p lt (insert n rt)


myTree : Tree
myTree = insert 1 (insert 5 (insert 3 leaf))

fromList : List -> Tree
fromList nil = leaf
fromList (x :: xs) = insert x (fromList xs)

-- introducing parametric polymorphism, implicit arguments in the 2nd step

foldr : {X : Set} -> (Nat -> X -> X) -> X -> List -> X
foldr f x nil = x
foldr f y (x :: xs) = f x (foldr f y xs)

-- toList (fromList2 numbers)

sort : List -> List
sort xs = toList (foldr insert leaf xs)

numbers : List
numbers = 14 :: 12 :: 68 :: 28 :: 3 :: 70 :: 30 :: 9 :: 8 :: 2 :: nil


-- ========== Truth as Type (rather than value) ==========

-- 1st definition
-- data _<='_ : Nat -> Nat -> Set where
--   0<='  : (y : Nat) -> 0 <=' y
--   1+<=' : (x y : Nat) -> x <=' y -> (1+ x) <=' (1+ y)

-- Reformulation of <=' as Zero,One-valued function:
-- The main (only?) benefit is to slightly simplify compare...
-- ... and we never need it in pattern mathcing "on the left".

Two = Boole
data One : Set where unit : One
data Zero : Set where

_<='_ : Nat -> Nat -> Set
zero <=' y = One
1+ x <=' zero = Zero
1+ x <=' 1+ y = x <=' y

data Bound : Set where
  bottom : Bound
  value : Nat -> Bound
  top : Bound

-- data _<B=_ : Bound -> Bound -> Set where
--   [<B : (y : Bound) -> bottom <B= y
--   <B< : (x y : Nat) -> x <=' y -> (value x) <B= (value y)
--   <B] : (x : Bound) -> x <B= top

_<B=_ : Bound -> Bound -> Set
bottom  <B= _       = One
value x <B= value y = x <=' y
_       <B= top     = One
_       <B= _       = Zero

data BST (l u : Bound) : Set where
  leaf : l <B= u -> BST l u
  node : (p : Nat)
    -> BST l (value p)
    -> BST (value p) u
    -> BST l u


-- BEGIN aside --------------------------------------------------

trans<=B : {l m u : Bound} -> l <B= m -> m <B= u -> l <B= u
trans<=B lm mu = {!!}

nonEmpty : {l u : Bound} (t : BST l u) -> l <B= u
nonEmpty (leaf lu) = lu
nonEmpty (node p lt rt) = {!!}

data _inT_ {l u : Bound} (x : Nat) : (t : BST l u) -> Set where
  inNode :
       (lt : BST l (value x))
    -> (rt : BST (value x) u)
    -> x inT (node x lt rt)
  inL : (y : Nat)
    -> (lt : BST l (value y))
    -> (rt : BST (value y) u)
    -> (x inT lt)
    -> x inT (node y lt rt)
  inR : (y : Nat)
    -> (lt : BST l (value y))
    -> (rt : BST (value y) u)
    -> (x inT rt)
    -> x inT (node y lt rt)

boundedL : {l u : Bound} -> (t : BST l u) -> (x : Nat) -> x inT t -> l <B= value x
boundedL {l} {u} (node p lt rt) .p (inNode .lt .rt) = {!!}
boundedL {l} {u} (node p lt rt) x (inL .p .lt .rt xint) = {!!}
boundedL {l} {u} (node p lt rt) x (inR .p .lt .rt xint) = {!!}


-- END aside --------------------------------------------------

data Total (x y : Nat) : Set where
  is<= : x <=' y -> Total x y
  is>= : y <=' x -> Total x y

compare : (x y : Nat) -> Total x y
compare zero y = is<= unit
compare (1+ x) zero = is>= unit
compare (1+ x) (1+ y) with compare x y
... | is<= xy = is<= xy
... | is>= yx = is>= yx


insertBST : {l u : Bound}
  -> (x : Nat)
  -> l <B= (value x)
  -> (value x) <B= u
  -> BST l u
  -> BST l u
insertBST x lx xu (leaf lu) = node x (leaf lx) (leaf xu)
insertBST x lx xu (node y lt rt) with compare x y
... | is<= xy = node y (insertBST x lx xy lt) rt
... | is>= yx = node y lt (insertBST x yx xu rt)

{- REMINDER
insert : Nat → Tree → Tree
insert n leaf = node n leaf leaf
insert n (node p lt rt) with n <= p
... | true = node p (insert n lt) rt
... | false = node p lt (insert n rt)
-}

myBST myBST2 : BST bottom top
myBST = node 3 (node 1 (leaf unit) (leaf unit)) (node 5 (leaf unit) (leaf unit))
myBST2 = insertBST 5 unit unit (insertBST 1 unit unit (insertBST 3 unit unit (leaf unit)))

-- sort xs = toList (foldr insert leaf xs)
fromListBST : List -> BST bottom top
-- fromListBST = λ l → foldr (λ x m → insertBST x unit unit m) (leaf unit) l
fromListBST = foldr (λ x → insertBST x unit unit) (leaf unit)

-- fromListBST numbers

data OList (l u : Bound) : Set where
  nil : l <B= u -> OList l u
  cons : (x : Nat) -> l <B= value x -> OList (value x) u -> OList l u

myOList : OList bottom top
myOList = cons 1 unit (cons 3 unit (cons 5 unit (nil unit)))

{- REMINDER
append : List -> List -> List
append nil l = l
append (x :: xs) l = x :: (append xs l)
-}

-- ... "with weird f"
appendOList : {l n u : Bound}
  -> OList l n
  -> ({m : Bound} -> m <B= n -> OList m u)
  -> OList l u
appendOList (nil x) f = f x
appendOList (cons x lx xs) f = cons x lx (appendOList xs (λ mn → f mn))

{-
toList : Tree -> List
toList leaf = nil
toList (node p lt rt) = append (toList lt) (p :: toList rt)
-}

toOListBST : {l u : Bound} -> BST l u -> OList l u
toOListBST (leaf lu) = nil lu
toOListBST (node x lt rt) = appendOList (toOListBST lt) (λ mx → cons x mx (toOListBST rt))

sortBST : List -> OList bottom top
sortBST l = toOListBST (fromListBST l) 

