module STLC3 where 

open import Data.Nat
-- open import Data.List
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary 
open import Data.Product


-- de Bruijn indexed lambda calculus
infix  5 ƛ_
infixl 7 _∙_
infix  9 var_

-- indexed by the number of binders out there
data Term : ℕ → Set where
  -- if x < n 
  --  then var x is bound 
  --  else var x is free 
  var_ : ∀ {n} → (x : ℕ) → Term n

  ƛ_ : ∀ {n} → Term (suc n) → Term n

  _∙_ : ∀ {n} → Term n → Term n → Term n


-- only "shift" the variable when 
--  1. it's free
--  2. it will be captured after substitution
shift : ∀ {n} → ℕ → Term n → Term (suc n)
shift {n} depth (var x) with n >? x 
shift {n} depth (var x) | yes p = var x -- bound 
shift {n} depth (var x) | no ¬p with depth >? x 
shift {n} depth (var x) | no ¬p | yes q = var (suc x) -- will be captured, should increment
shift {n} depth (var x) | no ¬p | no ¬q = var x -- safe from being captured
shift depth (ƛ M) = ƛ shift (suc depth) M
shift depth (M ∙ N) = shift depth M ∙ shift depth N


infixl 10 _[_/_]
_[_/_] : ∀ {n} → Term (suc n) → Term n → ℕ → Term n
(var x)   [ N / n ] with x ≟ n 
(var x)   [ N / n ] | yes p = N
(var x)   [ N / n ] | no ¬p = var x
(ƛ M)     [ N / n ] = ƛ (M [ shift (suc n) N / suc n ])
(L ∙ M)   [ N / n ] = L [ N / n ] ∙ M [ N / n ]

-- substitution
infixl 10 _[_]
_[_] : ∀ {n} → Term (suc n) → Term n → Term n
M [ N ] = M [ N / zero ]

-- β reduction
infix 3 _β→_
data _β→_ {n : ℕ} : Term n → Term n → Set where 

  β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ M [ N ]

  β-ƛ : ∀ {M N} → M β→ N → ƛ M β→ ƛ N

  β-∙-l : ∀ {L M N} → M β→ N → M ∙ L β→ N ∙ L

  β-∙-r : ∀ {L M N} → M β→ N → L ∙ M β→ L ∙ N



-- the reflexive and transitive closure of _β→_
infix  2 _β→*_ 
infixr 4 _→*_
data _β→*_ {n : ℕ} : Term n → Term n → Set where
  

  ∎ : ∀ {M} → M β→* M 
    
  _→*_ : ∀ {L M N}
    → L β→  M
    → M β→* N       
    --------------
    → L β→* N


infixl  3 _<β>_ 
_<β>_ : ∀ {n} {M N O : Term n} → M β→* N → N β→* O → M β→* O
∎          <β> N→O = N→O
L→M →* M→N <β> N→O = L→M →* (M→N <β> N→O)


hop : ∀ {n} {M N : Term n} → M β→ N → M β→* N
hop M→N = M→N →* ∎


-- infix  2 _-↠_ 

infixr 2 _→⟨_⟩_
_→⟨_⟩_
  : ∀ {n} {M N : Term n}
  → ∀ L
  → L β→ M       
  → M β→* N       
  --------------
  → L β→* N
L →⟨ P ⟩ Q = P →* Q

infixr 2 _→*⟨_⟩_
_→*⟨_⟩_
  : ∀ {n} {M N : Term n}
  → ∀ L
  → L β→* M       
  → M β→* N       
  --------------
  → L β→* N
L →*⟨ P ⟩ Q = P <β> Q

infix 3 _→∎
_→∎ : ∀ {n} (M : Term n) → M β→* M 
M →∎ = ∎


-- the symmetric closure of _β→*_

infix  1 _β≡_ 
data _β≡_ {n : ℕ} : Term n → Term n → Set where
  β-sym : ∀ {M N}
    → M β→* N
    → N β→* M
    -------
    → M β≡ N


infixr 2 _=*⟨_⟩_
_=*⟨_⟩_
  : ∀ {n} {M N : Term n} 
  → ∀ L
  → L β≡ M       
  → M β≡ N       
  --------------
  → L β≡ N
L =*⟨ β-sym A B ⟩ β-sym C D = β-sym (A <β> C) (D <β> B)

infixr 2 _=*⟨⟩_
_=*⟨⟩_
  : ∀ {n} {N : Term n}          
  → ∀ L
  → L β≡ N      
  --------------
  → L β≡ N
L =*⟨⟩ β-sym C D = β-sym C D

infix 3 _=∎
_=∎ : ∀ {n} → (M : Term n) → M β≡ M 
M =∎ = β-sym ∎ ∎


forward : ∀ {n} {M N : Term n} → M β≡ N → M β→* N
forward (β-sym A _) = A

backward : ∀ {n} {M N : Term n} → M β≡ N → N β→* M
backward (β-sym _ B) = B

-- data Normal : Set where 

Normal : ∀ {n} → Term n → Set 
Normal M = ¬ ∃ (λ N → M β→ N)

normal : ∀ {n} {M N : Term n} → Normal M → M β→* N → M ≡ N 
normal P ∎            = refl
normal P (M→L →* L→N) = ⊥-elim (P (_ , M→L))


cong-ƛ : ∀ {n} {M N : Term (suc n)} → M β→* N → ƛ M β→* ƛ N
cong-ƛ ∎            = ∎
cong-ƛ (M→N →* N→O) = β-ƛ M→N →* cong-ƛ N→O

cong-∙-l : ∀ {n} {L M N : Term n} → M β→* N → M ∙ L β→* N ∙ L
cong-∙-l ∎            = ∎
cong-∙-l (M→N →* N→O) = β-∙-l M→N →* cong-∙-l N→O

cong-∙-r : ∀ {n} {L M N : Term n} → M β→* N → L ∙ M β→* L ∙ N
cong-∙-r ∎            = ∎
cong-∙-r (M→N →* N→O) = β-∙-r M→N →* cong-∙-r N→O

cong-shift2 : ∀ {n i} {M N : Term n} → M β→* N → shift (suc i) M β→* shift (suc i) N
cong-shift2 {n} {i} {var x} {var y} M→N = {!   !}
cong-shift2 {n} {i} {var x} {ƛ N} M→N = {!   !}
cong-shift2 {n} {i} {var x} {N ∙ O} M→N = {!   !}
cong-shift2 {n} {i} {ƛ M} {var x} M→N = {!   !}
cong-shift2 {n} {i} {ƛ M} {ƛ N} M→N = {!   !}
cong-shift2 {n} {i} {ƛ M} {N ∙ O} M→N = {!   !}
cong-shift2 {n} {i} {M ∙ L} {var x} M→N = {!   !}
cong-shift2 {n} {i} {M ∙ L} {ƛ N} M→N = {!   !}
cong-shift2 {n} {i} {M ∙ L} {.M ∙ .L} ∎ = ∎
cong-shift2 {n} {i} {M ∙ L} {N ∙ O} (_→*_ {M = K} M∙L→K K→N∙O) =
    shift (suc i) (M ∙ L)
  →*⟨ {!   !} ⟩ 
    shift (suc i) K
  →*⟨ cong-shift2 K→N∙O ⟩ 
    shift (suc i) (N ∙ O)
  →∎
-- cong-shift2 {n} {i} {ƛ M} {ƛ N} ((β-ƛ M→N) →* ∎) = β-ƛ (cong-shift2 (hop M→N))
-- cong-shift2 {n} {i} {M ∙ L} {var x} M→N = {!   !}
-- cong-shift2 {n} {i} {M ∙ L} {ƛ N} M→N = {!   !}
-- cong-shift2 {n} {i} {M ∙ L} {N ∙ K} M→N = {!   !}


cong-shift3 : ∀ {n i} {M N : Term n} → M β→ N → shift (suc i) M β→ shift (suc i) N
cong-shift3 {n} {i} {ƛ M} {ƛ N} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ L} {var x} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ L} {ƛ N} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ var x₁} {var x₂ ∙ var x₃} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ var x₁} {var x₂ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ var x₁} {var x₂ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ var x₁} {(ƛ N) ∙ var x₂} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ var x₁} {N ∙ N₁ ∙ var x₂} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (ƛ L)} {var x₁ ∙ var x₂} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (ƛ L)} {var x₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (ƛ L)} {var x₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (ƛ L)} {(ƛ N) ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (ƛ L)} {N ∙ N₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (L ∙ L₁)} {var x₁ ∙ var x₂} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (L ∙ L₁)} {var x₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (L ∙ L₁)} {var x₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (L ∙ L₁)} {(ƛ N) ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {var x ∙ (L ∙ L₁)} {N ∙ N₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {var x₁ ∙ var x₂} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {var x₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {var x₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {(ƛ N) ∙ var x₁} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {(ƛ N) ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {(ƛ N) ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {N ∙ N₁ ∙ var x₁} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {N ∙ N₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ var x} {N ∙ N₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {var x ∙ var x₁} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {var x ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {var x ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {(ƛ N) ∙ var x} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {(ƛ N) ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {(ƛ N) ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {N ∙ N₁ ∙ var x} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {N ∙ N₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (ƛ L)} {N ∙ N₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {var x ∙ var x₁} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {var x ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {var x ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {(ƛ N) ∙ var x} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {(ƛ N) ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {(ƛ N) ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {N ∙ N₁ ∙ var x} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {N ∙ N₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {(ƛ M) ∙ (L ∙ L₁)} {N ∙ N₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ var x} {var x₁ ∙ var x₂} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ var x} {(ƛ N) ∙ var x₁} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ var x} {N ∙ N₁ ∙ var x₁} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ var x} {N ∙ N₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ var x} {N ∙ N₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (ƛ L)} {var x ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (ƛ L)} {(ƛ N) ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (ƛ L)} {N ∙ N₁ ∙ var x} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (ƛ L)} {N ∙ N₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (ƛ L)} {N ∙ N₁ ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (L ∙ L₁)} {var x ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (L ∙ L₁)} {(ƛ N) ∙ (O ∙ O₁)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (L ∙ L₁)} {N ∙ N₁ ∙ var x} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (L ∙ L₁)} {N ∙ N₁ ∙ (ƛ O)} M→N = {!   !}
cong-shift3 {n} {i} {M ∙ M₁ ∙ (L ∙ L₁)} {N ∙ N₁ ∙ (O ∙ O₁)} M→N = {!   !}

cong-shift : ∀ {n i} {M N : Term n} → M β→ N → shift (suc i) M β→ shift (suc i) N
cong-shift {n} (β-ƛ-∙ {var x} {var y}) with suc n >? x 
cong-shift {n} (β-ƛ-∙ {var x} {var y}) | yes p with suc y ≤? n 
cong-shift {n} (β-ƛ-∙ {var zero} {var y}) | yes p | yes q with n >? y 
cong-shift {n} (β-ƛ-∙ {var zero} {var y}) | yes p | yes q | yes r = β-ƛ-∙
cong-shift {n} (β-ƛ-∙ {var zero} {var y}) | yes p | yes q | no ¬r = ⊥-elim (¬r q)
cong-shift {n} (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q with n >? suc x 
cong-shift {n} (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | yes r = {!   !} -- dump
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | no ¬r with suc i >? suc x 
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | no ¬r | yes s = {!   !} -- fishy
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | no ¬r | no ¬s = {!   !} -- dump
cong-shift {n} {i} (β-ƛ-∙ {var x} {var y}) | yes p | no ¬q with suc i >? y 
cong-shift {n} {i} (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r with n >? y 
cong-shift {n} {i} (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | yes s = ⊥-elim (¬q s)
cong-shift {n} {i} (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | no ¬s with suc i >? y 
cong-shift {n} {i} (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | no ¬s | yes t = β-ƛ-∙
cong-shift {n} {i} (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | no ¬s | no ¬t = ⊥-elim (¬t r)
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r with n >? suc x 
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | yes t = {!   !} -- dump 
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | no ¬t with suc i >? suc x
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | no ¬t | yes u = {!   !} -- fishy 
cong-shift {n} {i} (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | no ¬t | no ¬u = β-ƛ-∙
cong-shift {n} {i} (β-ƛ-∙ {var x} {var y}) | yes p | no ¬q | no ¬r = {!   !}
cong-shift {n} (β-ƛ-∙ {var x} {var y}) | no ¬p = {!   !}
cong-shift {n} (β-ƛ-∙ {var x} {ƛ N}) = {!   !}
cong-shift {n} (β-ƛ-∙ {var x} {N ∙ O}) = {!   !}
-- cong-shift {n} (β-ƛ-∙ {var x} {N}) with suc n >? x 
-- cong-shift {n} (β-ƛ-∙ {var zero} {N}) | yes p = β-ƛ-∙
-- cong-shift {n} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) with n >? suc x 
-- cong-shift {n} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | yes q = {!   !}
-- cong-shift {n} {i} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | no ¬q with suc i >? suc x 
-- cong-shift {n} {i} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | no ¬q | yes r = {!   !} -- fishy
-- cong-shift {n} {i} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | no ¬q | no ¬r = {!   !}
-- cong-shift {n} (β-ƛ-∙ {var zero} {var x}) | no ¬p = {!   !}
-- cong-shift {n} (β-ƛ-∙ {var zero} {ƛ N}) | no ¬p = {!   !}
-- cong-shift {n} (β-ƛ-∙ {var zero} {N ∙ O}) | no ¬p = {!   !}
-- cong-shift {n} (β-ƛ-∙ {var suc x} {N}) | no ¬p = {!   !}
cong-shift (β-ƛ-∙ {ƛ M} {N}) = {!   !}
cong-shift (β-ƛ-∙ {L ∙ var x} {N}) = {!   !}
cong-shift (β-ƛ-∙ {L ∙ (ƛ M)} {N}) = {!   !}
cong-shift (β-ƛ-∙ {L ∙ (M ∙ K)} {N}) = {!   !}
cong-shift (β-ƛ M→N) = β-ƛ (cong-shift M→N)
cong-shift (β-∙-l M→N) = β-∙-l (cong-shift M→N)
cong-shift (β-∙-r M→N) = β-∙-r (cong-shift M→N) 

cong-[] : ∀ {n i} {M N : Term n} → (L : Term (suc n)) → M β→ N → L [ M / i ] β→* L [ N / i ]
cong-[] {i = i} (var x) M→N with x ≟ i
cong-[] {i = i} (var x) M→N | yes p = hop M→N
cong-[] {i = i} (var x) M→N | no ¬p = ∎
cong-[] (ƛ L) M→N = cong-ƛ (cong-[] L (cong-shift M→N))
cong-[] {i = i} {M} {N} (L ∙ K) M→N =
    L [ M / i ] ∙ K [ M / i ] 
  →*⟨ cong-∙-l (cong-[] L M→N) ⟩ 
    L [ N / i ] ∙ K [ M / i ] 
  →*⟨ cong-∙-r (cong-[] K M→N) ⟩ 
    L [ N / i ] ∙ K [ N / i ] 
  →∎


cong-[]* : ∀ {n i} {M N : Term n} → (L : Term (suc n)) → M β→* N → L [ M / i ] β→* L [ N / i ]
cong-[]* {i = i} (var x) M→N with x ≟ i 
cong-[]* {i = i} (var x) M→N | yes p = M→N
cong-[]* {i = i} (var x) M→N | no ¬p = ∎
cong-[]* (ƛ L) M→N = cong-ƛ (cong-[]* L (cong-shift2 M→N))
cong-[]* {i = i} {M} {N} (L ∙ K) M→N =
    L [ M / i ] ∙ K [ M / i ] 
  →*⟨ cong-∙-l (cong-[]* L M→N) ⟩ 
    L [ N / i ] ∙ K [ M / i ] 
  →*⟨ cong-∙-r (cong-[]* K M→N) ⟩ 
    L [ N / i ] ∙ K [ N / i ] 
  →∎
-- L [ M / i ] ∙ K [ M / i ] β→* L [ N / i ] ∙ K [ N / i ]


module Temp where
  -- normal-ƛ : ∀ {n} {M : Term (suc n)} → Normal (ƛ M) → Normal M
  -- normal-ƛ P (N , M→N) = P ((ƛ N) , (β-ƛ M→N))

  -- normal-ƛ' : ∀ {n} {M : Term (suc n)} → Normal M → Normal (ƛ M)
  -- normal-ƛ' P (.(ƛ N) , β-ƛ {N = N} ƛM→N) = P (N , ƛM→N)

  -- normal-∙-r : ∀ {n} {M N : Term n} → Normal (M ∙ N) → Normal N
  -- normal-∙-r {_} {M} P (O , N→O) = P (M ∙ O , (β-∙-r N→O))

  -- normal-∙-l : ∀ {n} {M N : Term n} → Normal (M ∙ N) → Normal M
  -- normal-∙-l {_} {_} {N} P (O , M→O) = P (O ∙ N , (β-∙-l M→O))


  -- cong-ƛ : ∀ {n} {M N : Term (suc n)} → M β→* N → ƛ M β→* ƛ N
  -- cong-ƛ ∎            = ∎
  -- cong-ƛ (M→N →* N→O) = β-ƛ M→N →* cong-ƛ N→O

  -- cong-∙-l : ∀ {n} {L M N : Term n} → M β→* N → M ∙ L β→* N ∙ L
  -- cong-∙-l ∎            = ∎
  -- cong-∙-l (M→N →* N→O) = β-∙-l M→N →* cong-∙-l N→O

  -- cong-∙-r : ∀ {n} {L M N : Term n} → M β→* N → L ∙ M β→* L ∙ N
  -- cong-∙-r ∎            = ∎
  -- cong-∙-r (M→N →* N→O) = β-∙-r M→N →* cong-∙-r N→O

  -- lemma-1 : ∀ {n} (i : ℕ) (L : Term n) → (ƛ shift (suc i) L) ∙ L β→* var suc i
  -- lemma-1 {n} i (var x) with n >? x 
  -- lemma-1 {.(suc _)} i (var .0) | yes (s≤s z≤n) = {!   !}
  -- lemma-1 {.(suc (suc _))} i (var .(suc _)) | yes (s≤s (s≤s p)) = {!   !}
  --   --   (ƛ var x) ∙ var x
  --   -- →⟨ β-ƛ-∙ ⟩ 
  --   --   (var x) [ var x ] 
  --   -- →⟨ {!   !} ⟩
  --   --   {!   !} 
  --   -- →⟨ {!   !} ⟩ 
  --   --   {!   !} 
  --   -- →⟨ {!   !} ⟩ 
  --   --   var suc i 
  --   -- →∎
  -- -- (ƛ var x) ∙ var x β→* var suc i  
  -- lemma-1 {n} i (var x) | no ¬p = {!   !}
  -- lemma-1 {n} i (ƛ L) = {!   !}
  -- lemma-1 {n} i (L ∙ M) = {!   !}


  -- prop : ∀ {n} (i : ℕ) (L : Term n) (N : Term (suc n))
  --   → (M : Term (suc (suc n)))
  --   → ((ƛ M) [ L / i ]) ∙ N [ L / i ] β→* M [ N ] [ L / i ]
  -- prop i L N M = {!   !}

  -- cong-[]2 : ∀ {n i} {L : Term n} {M N : Term (suc n)} → M β→ N → (M [ L / i ]) β→* (N [ L / i ])
  -- cong-[]2 (β-ƛ-∙ {M}) = prop _ _ _ M
  -- cong-[]2 (β-ƛ M→N) = cong-ƛ (cong-[]2 M→N)
  -- cong-[]2 (β-∙-l M→N) = cong-∙-l (cong-[]2 M→N)
  -- cong-[]2 (β-∙-r M→N) = cong-∙-r (cong-[]2 M→N)


β→confluent :  ∀ {n} (M N O : Term n) → (M β→ N) → (M β→ O) → ∃ (λ P → (N β→* P) × (O β→* P))
β→confluent .((ƛ M) ∙ N) _ _ (β-ƛ-∙ {M} {N}) β-ƛ-∙ = (M [ N ]) , (∎ , ∎)
β→confluent .((ƛ M) ∙ N) _ .(O ∙ N) (β-ƛ-∙ {M} {N}) (β-∙-l {N = O} M→O) = (O ∙ N) , ({!   !} , ∎)
β→confluent .((ƛ M) ∙ N) _ .((ƛ M) ∙ O) (β-ƛ-∙ {M} {N}) (β-∙-r {N = O} N→O) = (M [ O ]) , (cong-[]* M (hop N→O) , (hop β-ƛ-∙))
β→confluent .(ƛ M) .(ƛ N) .(ƛ O) (β-ƛ {M} {N} M→N) (β-ƛ {N = O} M→O) with β→confluent M N O M→N M→O 
β→confluent .(ƛ M) .(ƛ N) .(ƛ O) (β-ƛ {M} {N} M→N) (β-ƛ {N = O} M→O) | P , N→P , O→P = (ƛ P) , ((cong-ƛ N→P) , (cong-ƛ O→P))
β→confluent .((ƛ M) ∙ L) .(N ∙ L) _ (β-∙-l {L} {N = N} M→N) (β-ƛ-∙ {M}) = (N ∙ L) , (∎ , {!   !})
β→confluent .(M ∙ L) .(N ∙ L) .(K ∙ L) (β-∙-l {L} {M} {N} M→N) (β-∙-l {N = K} M→O) with β→confluent M N K M→N M→O  
β→confluent .(M ∙ L) .(N ∙ L) .(K ∙ L) (β-∙-l {L} {M} {N} M→N) (β-∙-l {N = K} M→O) | P , N→P , K→P = P ∙ L , ((cong-∙-l N→P) , cong-∙-l K→P)
β→confluent .(M ∙ L) .(N ∙ L) .(M ∙ K) (β-∙-l {L} {M} {N} M→N) (β-∙-r {N = K} M→O) = N ∙ K , hop (β-∙-r M→O) , hop (β-∙-l M→N)
β→confluent .((ƛ L) ∙ M) .((ƛ L) ∙ N) _ (β-∙-r {M = M} {N} M→N) (β-ƛ-∙ {L}) = (L [ N ]) , (hop β-ƛ-∙ , cong-[]* L (hop M→N))
β→confluent .(K ∙ M) .(K ∙ N) .(L ∙ M) (β-∙-r {K} {M} {N} M→N) (β-∙-l {N = L} K→L) = (L ∙ N) , ((hop (β-∙-l K→L)) , hop (β-∙-r M→N))
β→confluent .(_ ∙ M) .(_ ∙ N) .(_ ∙ O) (β-∙-r {M = M} {N} M→N) (β-∙-r {N = O} M→O) with β→confluent M N O M→N M→O 
β→confluent .(L ∙ M) .(L ∙ N) .(L ∙ O) (β-∙-r {L} {M} {N} M→N) (β-∙-r {N = O} M→O) | P , N→P , O→P = (L ∙ P) , (cong-∙-r N→P , cong-∙-r O→P)

β→*-confluent :  ∀ {n} {M N O : Term n} → (M β→* N) → (M β→* O) → ∃ (λ P → (N β→* P) × (O β→* P))
β→*-confluent {n} {M} {.M} {O} ∎            M→O          = O , M→O , ∎
β→*-confluent {n} {M} {N} {.M} (M→L →* L→N) ∎            = N , ∎   , (M→L →* L→N)
β→*-confluent {n} {M} {N} {O}  (M→L →* L→N) (M→K →* K→O) = {!   !}



normal-unique : ∀ {n} {M N O : Term n} → Normal N → Normal O → M β→* N → M β→* O → N ≡ O
normal-unique P Q M→N M→O = let X = β→*-confluent M→N M→O in trans (normal P (proj₁ (proj₂ X))) (sym (normal Q (proj₂ (proj₂ X))))
