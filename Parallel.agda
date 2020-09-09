module Parallel where

open import Data.Nat

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



shift-var : (n i x : ℕ) → ℕ 
shift-var zero    i x       = x + i  -- free 
shift-var (suc n) i zero    = zero   -- bound
shift-var (suc n) i (suc x) = suc (shift-var n i x)

shift : (n i : ℕ) → Term → Term
shift n i (var x) = var (shift-var n i x)
shift n i (ƛ M)   = ƛ shift (suc n) i M
shift n i (M ∙ N) = shift n i M ∙ shift n i N

infixl 10 _[_/_]
_[_/_] : Term → Term → ℕ → Term
(var x) [ N / i ] with compare x i 
((var x) [ N / .(suc (x + k)) ])  | less .x k    = var x
((var x) [ N / .x ])              | equal .x     = shift 0 x N
((var .(suc (i + k))) [ N / i ])  | greater .i k = var (i + k)
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

cong-ƛ : {M N : Term} → M β→* N → ƛ M β→* ƛ N
cong-ƛ = gmap _ β-ƛ

cong-∙-l : {L M N : Term} → M β→* N → M ∙ L β→* N ∙ L
cong-∙-l = gmap _ β-∙-l

cong-∙-r : {L M N : Term} → M β→* N → L ∙ M β→* L ∙ N
cong-∙-r = gmap _ β-∙-r 

cong-∙ : {M M' N N' : Term} → M β→* M' → N β→* N' → M ∙ N β→* M' ∙ N'
cong-∙ M→M' N→N' = (cong-∙-l M→M') ◅◅ (cong-∙-r N→N')


module Example where 

  open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using (preorder)
  open import Relation.Binary.Reasoning.Preorder (preorder _β→*_) 

  infixr 2 _→*⟨_⟩_
  _→*⟨_⟩_ : ∀ (x : Term) {y z} → x β→* y → y IsRelatedTo z → x IsRelatedTo z
  x →*⟨ P ⟩ y = x ∼⟨ return P ⟩ y

  infixr 2 _→⟨_⟩_
  _→⟨_⟩_ : ∀ (x : Term) {y z} → x β→ y → y IsRelatedTo z → x IsRelatedTo z
  x →⟨ P ⟩ y = x ∼⟨ return (return P) ⟩ y

  infixr 2 _→⟨⟩_
  _→⟨⟩_ : ∀ (x : Term) {y} → x IsRelatedTo y → x IsRelatedTo y
  x →⟨⟩ y = x ∼⟨ return ε ⟩ y

  test-1 : ((ƛ var 0) ∙ var 0) IsRelatedTo ((var 0) [ var 0 ])
  test-1 = (ƛ var 0) ∙ var 0 →⟨ β-ƛ-∙ ⟩ (var 0) [ var 0 ] ∎

  test-0 : ƛ (ƛ var 0 ∙ var 1) ∙ (ƛ var 0 ∙ var 1) IsRelatedTo ƛ var 0 ∙ var 0
  test-0 = 
          ƛ (ƛ var 0 ∙ var 1) ∙ (ƛ var 0 ∙ var 1)
      →⟨ β-ƛ β-ƛ-∙ ⟩ 
          ƛ (var 0 ∙ var 1) [ ƛ var 0 ∙ var 1 ]
      →⟨⟩ 
          ƛ (var 0 ∙ var 1) [ ƛ var 0 ∙ var 1 / 0 ]
      →⟨⟩ 
          ƛ (var 0) [ ƛ var 0 ∙ var 1 / 0 ] ∙ (var 1) [ ƛ var 0 ∙ var 1 / 0 ]
      →⟨⟩  
          ƛ shift 0 0 (ƛ var 0 ∙ var 1) ∙ var 0
      →⟨⟩  
          ƛ (ƛ shift 0 0 (var 0 ∙ var 1)) ∙ var 0
      →⟨⟩  
          ƛ (ƛ shift 0 0 (var 0) ∙ shift 0 0 (var 1)) ∙ var 0
      →⟨⟩  
          ƛ ((ƛ var 0 ∙ var 1) ∙ var 0)
      →⟨ β-ƛ β-ƛ-∙ ⟩  
          ƛ (var 0 ∙ var 1) [ var 0 / 0 ]
      →⟨⟩  
          ƛ var 0 ∙ var 0
      ∎ 
      
  Z : Term 
  Z = ƛ ƛ var 0

  SZ : Term 
  SZ = ƛ ƛ var 1 ∙ var 0

  PLUS : Term 
  PLUS = ƛ ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)

  test-2 : PLUS ∙ Z ∙ SZ IsRelatedTo SZ
  test-2 = 
      PLUS ∙ Z ∙ SZ
    →⟨ β-∙-l β-ƛ-∙ ⟩ 
      (ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 0 ] ∙ SZ
    →⟨⟩ 
      (ƛ ((ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 1 ])) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 2 ])) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ ((var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 3 ])))) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ (var 3) [ ƛ ƛ var 0 / 3 ] ∙ (var 1) [ ƛ ƛ var 0 / 3 ] ∙ (var 2 ∙ var 1 ∙ var 0) [ ƛ ƛ var 0 / 3 ]))) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ (shift 0 3 (ƛ (ƛ var 0))) ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ (ƛ (ƛ (var 0))) ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
    →⟨ β-∙-l (β-ƛ (β-ƛ (β-ƛ (β-∙-l β-ƛ-∙)))) ⟩ 
      (ƛ (ƛ (ƛ (ƛ var 0) [ var 1 / 0 ] ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ (ƛ (var 0) [ var 1 / 1 ]) ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ (ƛ var 0) ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
    →⟨ β-∙-l (β-ƛ (β-ƛ (β-ƛ β-ƛ-∙))) ⟩ 
      (ƛ (ƛ (ƛ (var 0) [ var 2 ∙ var 1 ∙ var 0 / 0 ]))) ∙ SZ
    →⟨⟩ 
      (ƛ (ƛ (ƛ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
    →⟨ β-ƛ-∙ ⟩ 
      (ƛ (ƛ (var 2 ∙ var 1 ∙ var 0))) [ SZ / 0 ]
    →⟨⟩ 
      ƛ (ƛ (var 2 ∙ var 1 ∙ var 0) [ SZ / 2 ])
    →⟨⟩ 
      ƛ (ƛ shift 0 2 SZ ∙ var 1 ∙ var 0)
    →⟨⟩ 
      ƛ (ƛ (ƛ ƛ var 1 ∙ var 0) ∙ var 1 ∙ var 0)
    →⟨ β-ƛ (β-ƛ (β-∙-l β-ƛ-∙)) ⟩ 
      ƛ (ƛ (ƛ var 1 ∙ var 0) [ var 1 / 0 ] ∙ var 0)
    →⟨⟩ 
      ƛ (ƛ (ƛ ((var 1 ∙ var 0) [ var 1 / 1 ])) ∙ var 0)
    →⟨⟩ 
      ƛ (ƛ (ƛ ((var 1) [ var 1 / 1 ] ∙ (var 0) [ var 1 / 1 ])) ∙ var 0)
    →⟨⟩ 
      ƛ (ƛ (ƛ (shift 0 1 (var 1) ∙ var 0)) ∙ var 0)
    →⟨⟩ 
      ƛ (ƛ (ƛ (var 2 ∙ var 0)) ∙ var 0)
    →⟨ β-ƛ (β-ƛ β-ƛ-∙) ⟩ 
      ƛ (ƛ (var 2 ∙ var 0) [ var 0 / 0 ])
    →⟨⟩ 
      ƛ (ƛ (var 2) [ var 0 / 0 ] ∙ var 0)
    →⟨⟩ 
      ƛ (ƛ var 1 ∙ var 0)
    ∎