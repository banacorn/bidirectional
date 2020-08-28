module STLC2 where 


open import Data.Nat
-- open import Data.List
-- open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary 


infix  5 ƛ_
infixl 7 _∙_
infix  9 var_
data Term : Set where
  var_ : ℕ → Term 

  ƛ_ : Term → Term 

  _∙_ : Term → Term → Term 

S : Term 
S = ƛ ƛ ƛ var 2 ∙ var 0 ∙ (var 1 ∙ var 0)

K : Term 
K = ƛ ƛ var 1

I : Term 
I = ƛ (var 0)

incr-var : Term → Term 
incr-var (var x) = var (suc x)
incr-var (ƛ M)   = ƛ M
incr-var (M ∙ N) = M ∙ N

incr-above : ℕ → Term → Term 
incr-above zero    (var x)     = var (suc x)
incr-above (suc n) (var zero)  = var zero
incr-above (suc n) (var suc x) = incr-var (incr-above n (var x))
incr-above n       (ƛ M)       = ƛ (incr-above (suc n) M)
incr-above n       (M ∙ N)     = incr-above n M ∙ incr-above n N

incr : Term → Term 
incr = incr-above zero 

decr-var : Term → Term 
decr-var (var x) = var (pred x)
decr-var (ƛ M)   = ƛ M
decr-var (M ∙ N) = M ∙ N

decr-above : ℕ → Term → Term 
decr-above zero (var x) = var pred x
decr-above (suc n) (var zero) = var zero
decr-above (suc n) (var suc x) = decr-var (decr-above n (var x))
decr-above n (ƛ M)   = ƛ decr-above (suc n) M
decr-above n (M ∙ N) = decr-above n M ∙ decr-above n N


decr : Term → Term 
decr = decr-above zero 


_[_/_] : Term → Term → ℕ → Term 
(var x)   [ N / n ] with x ≟ n 
(var x)   [ N / n ] | yes p = N
(var x)   [ N / n ] | no ¬p = var x
(ƛ M)     [ N / n ] = ƛ ((M [ N / suc n ]))
(L ∙ M)   [ N / n ] = L [ N / n ] ∙ M [ N / n ]


_[_] : Term → Term → Term 
M [ N ] = M [ N / zero ]

infix 3 _β→_
data _β→_ : Term → Term → Set where 

  β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ (M [ N ])

  β-ƛ : ∀ {M N} → M β→ N → ƛ M β→ ƛ N

  β-∙-l : ∀ {L M N} → M β→ N → M ∙ L β→ N ∙ L

  β-∙-r : ∀ {L M N} → M β→ N → L ∙ M β→ L ∙ N


data _β→*_ : Term → Term → Set where
  _∎ : ∀ M → M β→* M 

  _→⟨⟩_
    : ∀ L {M}          
    → L β→* M
    → L β→* M
    
  _→⟨_⟩_
    : ∀ L {M N}          
    → L β→ M       
    → M β→* N       
      -------
    → L β→* N

infix  2 _β→*_ 
infixr 2 _→⟨_⟩_
infixr 2 _→⟨⟩_
infix 3 _∎


Z : Term 
Z = ƛ ƛ var 0

SZ : Term 
SZ = ƛ ƛ var 1 ∙ var 0

PLUS : Term 
PLUS = ƛ ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)

test-0 : ƛ ((ƛ ƛ var 1) ∙ var 0) β→* ƛ ƛ (var 1)
test-0 = 
    ƛ ((ƛ ƛ var 1) ∙ var 0)
  →⟨ β-ƛ β-ƛ-∙ ⟩ 
    ƛ ((ƛ var 1) [ var 0 / 0 ])
  →⟨⟩ 
    ƛ (ƛ ((var 1) [ var 1 / 1 ]))
  →⟨⟩ 
    ƛ (ƛ var 1)
  ∎


test-1 : ƛ ((ƛ ƛ var 1) ∙ var 0) β→* ƛ ƛ (var 1)
test-1 = 
    ƛ ((ƛ ƛ var 1) ∙ var 0)
  →⟨ β-ƛ β-ƛ-∙ ⟩ 
    ƛ ((ƛ var 1) [ var 0 / 0 ])
  →⟨⟩ 
    ƛ (ƛ ((var 1) [ var 1 / 1 ]))
  →⟨⟩ 
    ƛ (ƛ var 1)
  ∎


test-2 : PLUS ∙ Z ∙ SZ β→* SZ
test-2 = 
    PLUS ∙ Z ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero))))) ∙ Z ∙ SZ
  →⟨ β-∙-l β-ƛ-∙ ⟩ 
    ((ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)))) [ Z ]) ∙ SZ
  →⟨⟩ 
    ((ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)))) [ Z / 0 ]) ∙ SZ
  →⟨⟩
    (ƛ ((ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero))) [ Z / 1 ])) ∙ SZ
  →⟨⟩
    (ƛ (ƛ ((ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ Z / 2 ]))) ∙ SZ
  →⟨⟩
    (ƛ ƛ ƛ ((var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ Z / 3 ])) ∙ SZ
  →⟨⟩
    (ƛ ƛ ƛ Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) ∙ SZ
  →⟨ β-ƛ-∙ ⟩ 
    ((ƛ ƛ Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ SZ / 0 ])
  →⟨⟩
    ƛ ((ƛ Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ SZ / 1 ])
  →⟨⟩
    ƛ ƛ ((Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ SZ / 2 ])
  →⟨⟩
    ƛ ƛ Z ∙ var 1 ∙ (SZ ∙ var 1 ∙ var 0)
  →⟨ β-ƛ (β-ƛ (β-∙-r (β-∙-l β-ƛ-∙))) ⟩ 
    ƛ ƛ Z ∙ var 1 ∙ (((ƛ var 1 ∙ var 0) [ var 1 / 0 ]) ∙ var 0)
  →⟨⟩
    ƛ ƛ Z ∙ var 1 ∙ ((ƛ ((var 1 ∙ var 0) [ var 1 / 1 ])) ∙ var 0)
  →⟨⟩
    ƛ ƛ Z ∙ var 1 ∙ ((ƛ (var 1 ∙ var 0)) ∙ var 0)
  →⟨ β-ƛ (β-ƛ (β-∙-r β-ƛ-∙)) ⟩ 
    ƛ ƛ Z ∙ var 1 ∙ ((var 1 ∙ var 0) [ var 0 / 0 ])
  →⟨⟩
    ƛ ƛ (ƛ ƛ var 0) ∙ var 1 ∙ (var 1 ∙ var 0)
  →⟨ β-ƛ (β-ƛ (β-∙-l β-ƛ-∙)) ⟩ 
    ƛ ƛ ((ƛ var 0) [ var 1 / 0 ]) ∙ (var 1 ∙ var 0)
  →⟨⟩ 
    ƛ ƛ (ƛ ((var 0) [ var 1 / 1 ])) ∙ (var 1 ∙ var 0)
  →⟨⟩ 
    ƛ ƛ (ƛ var 0) ∙ (var 1 ∙ var 0)
  →⟨ β-ƛ (β-ƛ β-ƛ-∙) ⟩ 
    ƛ ƛ ((var 0) [ var 1 ∙ var 0 / 0 ])
  →⟨⟩ 
    SZ 
  ∎