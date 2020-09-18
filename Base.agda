module Base where 

open import Data.Nat

--------------------------------------------------------------------------------
-- de Bruijn indexed lambda calculus
infix  5 ƛ_
infixl 7 _∙_
infix  9 var_

data Term : Set where
  var_  : (x : ℕ) → Term
  ƛ_    : (M : Term) → Term
  _∙_   : (M : Term) → (N : Term) → Term

