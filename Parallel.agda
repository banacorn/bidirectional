module Parallel where

open import Data.Nat
open import Data.Nat.Properties

--------------------------------------------------------------------------------
-- de Bruijn indexed lambda calculus
infix  5 ƛ_
infixl 7 _∙_
infix  9 var_

data Term : Set where
  var_  : (x : ℕ) → Term
  ƛ_    : (M : Term) → Term
  _∙_   :  (M : Term) → (N : Term) → Term


--------------------------------------------------------------------------------
-- substitution

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (preorder; [_]) 
open import Agda.Builtin.Bool

--------------------------------------------------------------------------------
-- shift-var 
--------------------------------------------------------------------------------

shift-var : (n i x : ℕ) → ℕ 
shift-var n i x with n ≤? x 
... | true  because ofʸ  p = i + x      -- free 
... | false because ofⁿ ¬p =     x      -- bound 


shift : (n i : ℕ) → Term → Term
shift n i (var x) = var (shift-var n i x)
shift n i (ƛ M)   = ƛ shift (suc n) i M
shift n i (M ∙ N) = shift n i M ∙ shift n i N

data Match : ℕ → ℕ → Set where
  Under : ∀ {i x} → x     < i → Match x       i
  Exact : ∀ {i x} → x     ≡ i → Match x       i
  Above : ∀ i v   → suc v > i → Match (suc v) i

open import Relation.Binary.Definitions

match : (x i : ℕ) → Match x i
match x       i with <-cmp x i 
match x       i | tri< a ¬b ¬c = Under a
match x       i | tri≈ ¬a b ¬c = Exact b
match (suc x) i | tri> ¬a ¬b c = Above i x c

subst-var : ∀ {x i} → Match x i → Term → Term 
subst-var {x}     (Under _)     N = var x
subst-var {_} {i} (Exact _)     N = shift 0 i N
subst-var         (Above _ x _) N = var x

infixl 10 _[_/_]
_[_/_] : Term → Term → ℕ → Term
(var x) [ N / i ] = subst-var (match x i) N
(ƛ M)   [ N / i ] = ƛ (M [ N / suc i ])
(L ∙ M) [ N / i ] = L [ N / i ] ∙ M [ N / i ]

-- substitute the 0th var in M for N
infixl 10 _[_]
_[_] : Term → Term → Term
M [ N ] = M [ N / 0 ]


--------------------------------------------------------------------------------
-- relations


-- β-reduction
infix 3 _β→_
data _β→_ : Term → Term → Set where 

  β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ (M [ N ])

  β-ƛ : ∀ {M N} → M β→ N → ƛ M β→ ƛ N

  β-∙-l : ∀ {L M N} → M β→ N → M ∙ L β→ N ∙ L

  β-∙-r : ∀ {L M N} → M β→ N → L ∙ M β→ L ∙ N

open import Relation.Binary.Construct.Closure.ReflexiveTransitive 

infix  2 _β→*_ 
_β→*_ : Term → Term → Set
_β→*_ = Star _β→_
{-# DISPLAY Star _β→_ = _β→*_ #-}

-- parallel β-reduction
infix 3 _β⇒_
data _β⇒_ : Term → Term → Set where 

  β-var : {n : ℕ} → var n β⇒ var n

  β-ƛ : ∀ {M M'} → (M⇒M' : M β⇒ M') → ƛ M β⇒ ƛ M'

  β-∙ : ∀ {M M' N N'} → (M⇒M' : M β⇒ M') → (N⇒N' : N β⇒ N') → M ∙ N β⇒ M' ∙ N'

  β-ƛ-∙ : ∀ {M M' N N'} → (M⇒M' : M β⇒ M') → (N⇒N' : N β⇒ N') → (ƛ M) ∙ N β⇒ M' [ N' ]

-- properties
β⇒identity : ∀ {M} → M β⇒ M
β⇒identity {var x} = β-var
β⇒identity {ƛ M}   = β-ƛ β⇒identity
β⇒identity {M ∙ N} = β-∙ β⇒identity β⇒identity

to-parallel : ∀ {M N} → M β→ N → M β⇒ N 
to-parallel β-ƛ-∙       = β-ƛ-∙ β⇒identity β⇒identity
to-parallel (β-ƛ M→N)   = β-ƛ (to-parallel M→N)
to-parallel (β-∙-l M→N) = β-∙ (to-parallel M→N) β⇒identity
to-parallel (β-∙-r M→N) = β-∙ β⇒identity (to-parallel M→N)

open import Relation.Binary.PropositionalEquality hiding ([_]; preorder)

cong-var : ∀ {x y} → x ≡ y → var x β→* var y
cong-var {x} {y} refl = ε

cong-ƛ : {M N : Term} → M β→* N → ƛ M β→* ƛ N
cong-ƛ = gmap _ β-ƛ

cong-∙-l : {L M N : Term} → M β→* N → M ∙ L β→* N ∙ L
cong-∙-l = gmap _ β-∙-l

cong-∙-r : {L M N : Term} → M β→* N → L ∙ M β→* L ∙ N
cong-∙-r = gmap _ β-∙-r 

cong-∙ : {M M' N N' : Term} → M β→* M' → N β→* N' → M ∙ N β→* M' ∙ N'
cong-∙ M→M' N→N' = (cong-∙-l M→M') ◅◅ (cong-∙-r N→N')

