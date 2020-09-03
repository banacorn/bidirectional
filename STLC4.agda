module STLC4 where 

open import Data.Nat
open import Data.Nat.Properties using (≤-antisym; ≤-trans; ≰⇒>; ≤-step)
-- open import Data.List
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary 
open import Data.Product


-- de Bruijn indexed lambda calculus
infix  5 ƛ_
infixl 7 _∙_
infix  9 var_

data Term : Set where
  var_  : (x : ℕ) → Term
  ƛ_    : Term → Term
  _∙_   :  Term → Term → Term


shift : (n i : ℕ) → Term → Term
shift free i (var x) with x ≥? free 
shift free i (var x) | yes p = var (x + i) -- free 
shift free i (var x) | no ¬p = var x -- bound
shift free i (ƛ M)   = ƛ shift (suc free) i M
shift free i (M ∙ N) = shift free i M ∙ shift free i N

infixl 10 _[_/_]
_[_/_] : Term → Term → ℕ → Term
(var x) [ N / i ] with compare x i 
((var x) [ N / .(suc (x + k)) ])  | less .x k = var x
((var x) [ N / .x ])              | equal .x = shift 0 x N
((var .(suc (i + k))) [ N / i ])  | greater .i k = var (i + k)
(ƛ M)   [ N / i ] = ƛ (M [ N / suc i ])
(L ∙ M) [ N / i ] = L [ N / i ] ∙ M [ N / i ]

-- substitute the 0th var in M for N
infixl 10 _[_]
_[_] : Term → Term → Term
M [ N ] = M [ N / 0 ]

-- β reduction
infix 3 _β→_
data _β→_ : Term → Term → Set where 

  β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ (M [ N ])

  β-ƛ : ∀ {M N} → M β→ N → ƛ M β→ ƛ N

  β-∙-l : ∀ {L M N} → M β→ N → M ∙ L β→ N ∙ L

  β-∙-r : ∀ {L M N} → M β→ N → L ∙ M β→ L ∙ N


module TransRefl where
  -- the reflexive and transitive closure of _β→_
  infix  2 _β→*_ 
  infixr 2 _→*_
  data _β→*_ : Term → Term → Set where

    ∎ : ∀ {M} → M β→* M 
        
    _→*_
      : ∀ {L M N}          
      → L β→ M       
      → M β→* N       
      --------------
      → L β→* N


  infixl 3 _<β>_ 
  _<β>_ : ∀ {M N O} → M β→* N → N β→* O → M β→* O
  _<β>_ {M} {.M} {O} ∎            N→O = N→O
  _<β>_ {M} {N}  {O} (L→M →* M→N) N→O = L→M →* M→N <β> N→O


  infixr 2 _→⟨⟩_
  _→⟨⟩_
    : ∀ {M}          
    → ∀ N
    → N β→* M
    --------------
    → N β→* M
  M →⟨⟩ Q = Q

  infixr 2 _→⟨_⟩_
  _→⟨_⟩_
    : ∀ {M N}          
    → ∀ L
    → L β→ M       
    → M β→* N       
    --------------
    → L β→* N
  L →⟨ P ⟩ Q = P →* Q

  infixr 2 _→*⟨_⟩_
  _→*⟨_⟩_
    : ∀ {M N}          
    → ∀ L
    → L β→* M       
    → M β→* N       
    --------------
    → L β→* N
  L →*⟨ P ⟩ Q = P <β> Q

  infix 3 _→∎
  _→∎ : ∀ M → M β→* M 
  M →∎ = ∎


  hop : ∀ {M N} → M β→ N → M β→* N
  hop {M} {N} M→N = M→N →* ∎


open TransRefl

-- the symmetric closure of _β→*_
module Eq where 
  infix  1 _β≡_ 
  data _β≡_ : Term → Term → Set where
    β-sym : ∀ {M N}
        → M β→* N
        → N β→* M
        -------
        → M β≡ N

  infixr 2 _=*⟨_⟩_
  _=*⟨_⟩_
    : ∀ {M N}          
    → ∀ L
    → L β≡ M       
    → M β≡ N       
    --------------
    → L β≡ N
  L =*⟨ β-sym A B ⟩ β-sym C D = β-sym (A <β> C) (D <β> B)

  infixr 2 _=*⟨⟩_
  _=*⟨⟩_
    : ∀ {N}          
    → ∀ L
    → L β≡ N      
    --------------
    → L β≡ N
  L =*⟨⟩ β-sym C D = β-sym C D

  infix 3 _=∎
  _=∎ : ∀ M → M β≡ M 
  M =∎ = β-sym ∎ ∎

  forward : ∀ {M N} → M β≡ N → M β→* N
  forward (β-sym A _) = A

  backward : ∀ {M N} → M β≡ N → N β→* M
  backward (β-sym _ B) = B



module Example where 

  test-1 : ƛ (ƛ var 1) ∙ var 0 β→* ƛ var 0
  test-1 = 
          ƛ (ƛ var 1) ∙ var 0
      →⟨ β-ƛ β-ƛ-∙ ⟩ 
          ƛ var 0
      →∎

  test-0 : ƛ (ƛ var 0 ∙ var 1) ∙ (ƛ var 0 ∙ var 1) β→* ƛ var 0 ∙ var 0
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
          ƛ (ƛ shift 1 0 (var 0 ∙ var 1)) ∙ var 0
      →⟨⟩  
          ƛ (ƛ shift 1 0 (var 0) ∙ shift 1 0 (var 1)) ∙ var 0
      →⟨⟩  
          ƛ ((ƛ var 0 ∙ var 1) ∙ var 0)
      →⟨ β-ƛ β-ƛ-∙ ⟩  
          ƛ (var 0 ∙ var 1) [ var 0 / 0 ]
      →⟨⟩  
          ƛ var 0 ∙ var 0
    →∎ 

  Z : Term 
  Z = ƛ ƛ var 0

  SZ : Term 
  SZ = ƛ ƛ var 1 ∙ var 0

  PLUS : Term 
  PLUS = ƛ ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)


  test-2 : PLUS ∙ Z ∙ SZ β→* SZ
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
      (ƛ (ƛ (ƛ (ƛ (ƛ var 0)) ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
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
    →∎