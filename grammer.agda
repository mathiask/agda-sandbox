-- 20201204 Mathias Kegelmann - Grammer Implementation in Agda

-- import Data.List
--   using
--   (List
--   ; []; _∷_
--   ; sum; map; take; reverse; _++_; drop
--   )

open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Bool

terminal? = primIsLower

not : Bool → Bool
not false = true
not true = false

nonterminal? = λ c → not (terminal? c)

data Rule : Set where
  _⇒_ : String → String → Rule

_ : Rule
_ = "hello" ⇒ "world"

data Grammar : Set where
  Γ : Char → List(Rule) → Grammar

klm : Grammar
klm = Γ 'S' ("S" ⇒ "SS"  ∷ "S" ⇒ "AP" ∷
            "PA" ⇒ "AP"  ∷
            "P"  ⇒ "bPZ" ∷ "P" ⇒ "bZ" ∷
            "Z"  ⇒ "Zc"  ∷ "Zc" ⇒ "c" ∷
            [])

