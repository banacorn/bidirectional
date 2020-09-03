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



-- lemmas 



cong-ƛ : {M N : Term} → M β→* N → ƛ M β→* ƛ N
cong-ƛ ∎            = ∎
cong-ƛ (M→N →* N→O) = β-ƛ M→N →* cong-ƛ N→O

cong-∙-l : {L M N : Term} → M β→* N → M ∙ L β→* N ∙ L
cong-∙-l ∎            = ∎
cong-∙-l (M→N →* N→O) = β-∙-l M→N →* cong-∙-l N→O

cong-∙-r : {L M N : Term} → M β→* N → L ∙ M β→* L ∙ N
cong-∙-r ∎            = ∎
cong-∙-r (M→N →* N→O) = β-∙-r M→N →* cong-∙-r N→O

-- shift-subst : ∀ freeM i n M N → (shift (suc (suc free)) i M) [ shift free i N / n ] β→* shift (suc free) i (M [ N / n ])

shift-subst : ∀ free i n M N → (shift (suc (suc free)) i M) [ shift free i N / n ] β→* shift (suc free) i (M [ N / n ])
shift-subst free i n (var x) N with compare x n 
shift-subst free i .(suc (x + k)) (var x) N | less .x k with x ≥? suc free 
shift-subst free i .(suc (x + k)) (var x) N | less .x k | yes p with suc (suc free) ≤? x 
shift-subst free i .(suc (x + k)) (var x) N | less .x k | yes p | yes q = ?
shift-subst free i .(suc (x + k)) (var x) N | less .x k | yes p | no ¬q = {!   !}
shift-subst free i .(suc (x + k)) (var x) N | less .x k | no ¬p = {!   !}
shift-subst free i n (var .n) N | equal .n = {!   !}
shift-subst free i n (var .(suc (n + k))) N | greater .n k = {!   !}
  --   (shift (suc (suc free)) i (var x)) [ shift free i N / n ]
  -- →*⟨ {!   !} ⟩ 
  --   {!   !}
  -- →*⟨ {!   !} ⟩ 
  --   {!   !}
  -- →*⟨ {!   !} ⟩ 
  --   shift (suc free) i ((var x) [ N / n ])
  -- →∎ 

-- (shift (suc (suc free)) i (var x) | x ≥? suc (suc free)) [ shift free i N / n ]

-- shift (suc free) i ((var x) [ N / n ] | compare x n)
shift-subst free i n (ƛ M) N = 
    ƛ (shift (suc (suc (suc free))) i M [ shift free i N / suc n ])
  →*⟨ cong-ƛ {! shift-subst (suc free) i (suc n) M N  !} ⟩ 
    {!   !}
  →*⟨ {!   !} ⟩ 
    ƛ (shift (suc (suc (suc free))) i M [ shift (suc free) i N / suc n ])
  →*⟨ cong-ƛ (shift-subst (suc free) i (suc n) M N) ⟩ 
    ƛ (shift (suc (suc free)) i (M [ N / suc n ]))
  →∎ 
shift-subst free i n (M ∙ L) N = 
    shift (suc (suc free)) i M [ shift free i N / n ] ∙ shift (suc (suc free)) i L [ shift free i N / n ]
  →*⟨ cong-∙-l (shift-subst free i n M N) ⟩ 
    shift (suc free) i (M [ N / n ]) ∙ shift (suc (suc free)) i L [ shift free i N / n ]
  →*⟨ cong-∙-r (shift-subst free i n L N) ⟩ 
    shift (suc free) i (M [ N / n ]) ∙ shift (suc free) i (L [ N / n ])
  →∎ 
  
-- shift-subst free i (M ∙ L) (var y) = 
--     shift (suc (suc free)) i M [ shift free i (var y) / 1 ] ∙ shift (suc (suc free)) i L [ shift free i (var y) / 1 ]
--   →*⟨ cong-∙-l (shift-subst free i M (var y)) ⟩ 
--     shift (suc free) i (M [ var y / 1 ]) ∙ shift (suc (suc free)) i L [ shift free i (var y) / 1 ]
--   →*⟨ cong-∙-r (shift-subst free i L (var y)) ⟩ 
--     shift (suc free) i (M [ var y / 1 ]) ∙ shift (suc free) i (L [ var y / 1 ])
--   →∎ 
-- shift-subst free i (M ∙ L) (ƛ N) = 
--     shift (suc (suc free)) i M [ ƛ shift (suc free) i N / 1 ] ∙ shift (suc (suc free)) i L [ ƛ shift (suc free) i N / 1 ]
--   →*⟨ cong-∙-l (shift-subst free i M (ƛ N)) ⟩ 
--     shift (suc free) i (M [ ƛ N / 1 ]) ∙ shift (suc (suc free)) i L [ ƛ shift (suc free) i N / 1 ]
--   →*⟨ cong-∙-r (shift-subst free i L (ƛ N)) ⟩ 
--     shift (suc free) i (M [ ƛ N / 1 ]) ∙ shift (suc free) i (L [ ƛ N / 1 ])
--   →∎ 
-- shift-subst free i (M ∙ L) (N ∙ O) = 
--     shift (suc (suc free)) i M [ shift free i N ∙ shift free i O / 1 ] ∙ shift (suc (suc free)) i L [ shift free i N ∙ shift free i O / 1 ] 
--   →*⟨ cong-∙-l (shift-subst free i M (N ∙ O)) ⟩ 
--     shift (suc free) i (M [ N ∙ O / 1 ]) ∙ shift (suc (suc free)) i L [ shift free i N ∙ shift free i O / 1 ]
--   →*⟨ cong-∙-r (shift-subst free i L (N ∙ O)) ⟩ 
--     shift (suc free) i (M [ N ∙ O / 1 ]) ∙ shift (suc free) i (L [ N ∙ O / 1 ])
--   →∎ 

cong-shift-app0 : (free i : ℕ) → (M N : Term) → shift free i ((ƛ M) ∙ N) β→* shift free i (M [ N ])
cong-shift-app0 free i (var x) N = {!   !}
cong-shift-app0 free i (ƛ M) N = 
    (ƛ (ƛ shift (suc (suc free)) i M)) ∙ shift free i N
  →*⟨ hop β-ƛ-∙ ⟩
    (ƛ shift (suc (suc free)) i M) [ shift free i N / 0 ]
  →⟨⟩
    ƛ (shift (suc (suc free)) i M) [ shift free i N / 1 ]
  →*⟨ cong-ƛ {!   !} ⟩
    ƛ shift (suc free) i (M [ N / 1 ])
  →∎
-- (ƛ (ƛ shift (suc (suc free)) i M)) ∙ shift free i N β→*
--       ƛ shift (suc free) i (M [ N / 1 ])
cong-shift-app0 free i (M ∙ L) N = {!   !}

cong-shift-app : (free i : ℕ) → (M N : Term) → shift free i ((ƛ M) ∙ N) β→* shift free i (M [ N ])
cong-shift-app free i (var x) (var y) = {!   !}
cong-shift-app free i (var x) (ƛ N)   = {!   !}
cong-shift-app free i (var x) (N ∙ O) = {!   !}
cong-shift-app free i (ƛ M)   (var y) = {!   !}
cong-shift-app free i (ƛ M)   (ƛ N)   = {!   !}
cong-shift-app free i (ƛ M)   (N ∙ O) = {!   !}
cong-shift-app free i (M ∙ L) (var y) = {!   !}
cong-shift-app free i (M ∙ L) (ƛ N)   = {!   !}
cong-shift-app free i (M ∙ L) (N ∙ O) = {!   !}


cong-shift : (free i : ℕ) → (M N : Term) → M β→ N → shift free i M β→* shift free i N
cong-shift free i (ƛ M) (ƛ N) (β-ƛ M→N) = cong-ƛ (cong-shift (suc free) i M N M→N)
cong-shift free i (.(ƛ M) ∙ N) .(M [ N / 0 ]) (β-ƛ-∙ {M}) = cong-shift-app free i M N
cong-shift free i (M ∙ L) .(N ∙ L) (β-∙-l {N = N} M→N) = cong-∙-l (cong-shift free i M N M→N)
cong-shift free i (M ∙ L) .(M ∙ N) (β-∙-r {N = N} M→N) = cong-∙-r (cong-shift free i L N M→N)

cong-[] : ∀ {i M N} (L : Term) → M β→ N → L [ M / i ] β→* L [ N / i ]
cong-[] {i} (var x) M→N with compare x i
cong-[] {.(suc (x + k))} (var x) M→N  | less .x k = ∎
cong-[] {.x} {M} {N} (var x) M→N | equal .x = cong-shift 0 x M N M→N
cong-[] {.m} (var .(suc (m + k))) M→N | greater m k = ∎
cong-[] (ƛ L) M→N = cong-ƛ (cong-[] L M→N)
cong-[] {i} {M} {N} (L ∙ K) M→N = 
    L [ M / i ] ∙ K [ M / i ]
  →*⟨ cong-∙-l (cong-[] L M→N) ⟩
    L [ N / i ] ∙ K [ M / i ]
  →*⟨ cong-∙-r (cong-[] K M→N) ⟩
    L [ N / i ] ∙ K [ N / i ]
  →∎

-- single-step
β→confluent : ∀ {M N O} → (M β→ N) → (M β→ O) → ∃ (λ P → (N β→* P) × (O β→* P))
β→confluent β-ƛ-∙ β-ƛ-∙ = {!   !}
β→confluent β-ƛ-∙ (β-∙-l M→O) = {!   !}
β→confluent β-ƛ-∙ (β-∙-r M→O) = {!   !}
β→confluent (β-ƛ M→N) (β-ƛ M→O) = {!   !}
β→confluent (β-∙-l M→N) β-ƛ-∙ = {!   !}
β→confluent (β-∙-l M→N) (β-∙-l M→O) = {!   !}
β→confluent (β-∙-l M→N) (β-∙-r M→O) = {!   !}
β→confluent (β-∙-r {M = M} {N} M→N) (β-ƛ-∙ {L}) = L [ N ] , (hop β-ƛ-∙) , cong-[] L M→N
β→confluent (β-∙-r {L} {M} {N} M→N) (β-∙-l {N = O} M→O) = O ∙ N , hop (β-∙-l M→O) , hop (β-∙-r M→N)
β→confluent (β-∙-r {M = M} {N} M→N) (β-∙-r {N = O} M→O) with β→confluent M→N M→O 
β→confluent (β-∙-r {L} {M} {N} M→N) (β-∙-r {N = O} M→O) | P , N→P , O→P = (L ∙ P) , cong-∙-r N→P , cong-∙-r O→P


-- β→confluent : (M N O : Term) → (M β→ N) → (M β→ O) → ∃ (λ P → (N β→* P) × (O β→* P))
-- β→confluent .((ƛ _) ∙ _) ._           ._            β-ƛ-∙ β-ƛ-∙ = {!   !}
-- β→confluent .((ƛ _) ∙ _) ._           .(_ ∙ _)      β-ƛ-∙ (β-∙-l M→O) = {!   !}
-- β→confluent .((ƛ _) ∙ _) ._           .((ƛ _) ∙ _)  β-ƛ-∙ (β-∙-r M→O) = {!   !}
-- β→confluent .(ƛ _)       .(ƛ _)       .(ƛ _)        (β-ƛ M→N) (β-ƛ M→O) = {!   !}
-- β→confluent .((ƛ _) ∙ _) .(_ ∙ _)     ._            (β-∙-l M→N) β-ƛ-∙ = {!   !}
-- β→confluent .(_ ∙ _)     .(_ ∙ _)     .(_ ∙ _)      (β-∙-l M→N) (β-∙-l M→O) = {!   !}
-- β→confluent .(_ ∙ _)     .(_ ∙ _)     .(_ ∙ _)      (β-∙-l M→N) (β-∙-r M→O) = {!   !}
-- β→confluent .((ƛ _) ∙ _) .((ƛ _) ∙ _) ._            (β-∙-r M→N) β-ƛ-∙ = {!   !}
-- β→confluent .(_ ∙ _)     .(_ ∙ _)     .(_ ∙ _)      (β-∙-r M→N) (β-∙-l M→O) = {!   !}
-- β→confluent .(_ ∙ M)     .(_ ∙ N)     .(_ ∙ O)      (β-∙-r {M = M} {N} M→N) (β-∙-r {N = O} M→O) with β→confluent M N O M→N M→O 
-- β→confluent .(_ ∙ M)     .(_ ∙ N)     .(_ ∙ O)      (β-∙-r {M = M} {N} M→N) (β-∙-r {N = O} M→O) | P , N→P , O→P = {!   !}