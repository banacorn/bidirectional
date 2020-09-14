module STLC3 where 

open import Data.Nat
open import Data.Nat.Properties using (≤-antisym; ≤-trans; ≰⇒>)
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

-- indexed by the number of binders out there
data Term : ℕ → Set where
  -- if x < n 
  --  then var x is bound 
  --  else var x is free 
  var_ : ∀ {n} → (x : ℕ) → Term n

  ƛ_ : ∀ {n} → Term (suc n) → Term n

  _∙_ : ∀ {n} → Term n → Term n → Term n


data Var : Set where  
  Bound : ∀ {n x} → (bound : n > x) → Var 
  FreeIncr : ∀ {n x depth} → (free : suc x ≰ n) → (prop : depth ≡ suc x) → Var 
  Free : ∀ {n x depth} →(free : suc x ≰ n) → (safe : suc x ≰ depth) → Var 

sort : (n x depth : ℕ) → suc n ≥ depth → Var 
sort n x depth P with n >? x 
sort n x depth P | yes p = Bound p
sort n x depth P | no ¬p with depth >? x 
sort n x depth P | no ¬p | yes q = FreeIncr ¬p (≤-antisym (≤-trans P (≰⇒> ¬p)) q)
sort n x depth P | no ¬p | no ¬q = Free ¬p ¬q

-- only "shift" the variable when 
--  1. it's free
--  2. it will be captured after substitution
shift : ∀ {n} → (i : ℕ) → suc n ≥ i → Term n → Term (suc n)
shift {n} depth P (var x) with sort n x depth P
shift {n} depth P (var x) | Bound bound = var x
shift {n} depth P (var x) | FreeIncr free prop = var suc x
shift {n} depth P (var x) | Free free safe = var x
shift depth P (ƛ M) = ƛ shift (suc depth) (s≤s P) M
shift depth P (M ∙ N) = shift depth P M ∙ shift depth P N


infixl 10 _[_/_/_]
_[_/_/_] : ∀ {n} → Term (suc n) → Term n → (i : ℕ) → n ≥ i → Term n
(var x)   [ N / i / n≥i ] with x ≟ i
(var x)   [ N / i / n≥i ] | yes p = N
(var x)   [ N / i / n≥i ] | no ¬p = var x
(ƛ M)     [ N / i / n≥i ] = ƛ (M [ shift (suc i) (s≤s n≥i) N / suc i / s≤s n≥i ])
(L ∙ M)   [ N / i / n≥i ] = L [ N / i / n≥i ] ∙ M [ N / i / n≥i ]

-- substitution
infixl 10 _[_]
_[_] : ∀ {n} → Term (suc n) → Term n → Term n
M [ N ] = M [ N / zero / z≤n ]

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

cong-shift! : ∀ {n i} (M : Term (suc n)) (N : Term n) → (n≥i : n ≥ i) → shift (suc i) (s≤s n≥i) ((ƛ M) ∙ N) β→ shift (suc i) (s≤s n≥i) (M [ N ])
cong-shift! (var x) N n≥i = {!   !}
cong-shift! (ƛ M) N n≥i = {!   !}
cong-shift! (M ∙ L) N n≥i = {!   !}

cong-shift : ∀ {n i} {M N : Term n} → (n≥i : n ≥ i) → M β→ N → shift (suc i) (s≤s n≥i) M β→ shift (suc i) (s≤s n≥i) N
cong-shift n≥i (β-ƛ-∙ {M} {N}) = cong-shift! M N n≥i
cong-shift n≥i (β-ƛ M→N) = β-ƛ (cong-shift (s≤s n≥i) M→N)
cong-shift n≥i (β-∙-l M→N) = β-∙-l (cong-shift n≥i M→N)
cong-shift n≥i (β-∙-r M→N) = β-∙-r (cong-shift n≥i M→N)

-- cong-shift : ∀ {n i} {M N : Term n} → n ≥ i → M β→ N → shift (suc i) M β→ shift (suc i) N
-- cong-shift {n} n≥i (β-ƛ-∙ {var x} {var y}) with suc n >? x 
-- cong-shift {n} n≥i (β-ƛ-∙ {var x} {var y}) | yes p with suc y ≤? n 
-- cong-shift {n} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | yes q with n >? y 
-- cong-shift {n} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | yes q | yes r = β-ƛ-∙
-- cong-shift {n} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | yes q | no ¬r = ⊥-elim (¬r q)
-- cong-shift {n} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q with n >? suc x 
-- cong-shift {n} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | yes r = {!   !} -- dump
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | no ¬r with suc i >? suc x 
-- -- ≤-antisym p 
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | no ¬r | yes s = {! (≰⇒> ¬r)  !} -- fishy
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | yes q | no ¬r | no ¬s = {!   !} -- dump
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var x} {var y}) | yes p | no ¬q with suc i >? y 
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r with n >? y 
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | yes s = ⊥-elim (¬q s)
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | no ¬s with suc i >? y 
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | no ¬s | yes t = β-ƛ-∙
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var zero} {var y}) | yes p | no ¬q | yes r | no ¬s | no ¬t = ⊥-elim (¬t r)
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r with n >? suc x 
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | yes t = {!   !} -- dump 
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | no ¬t with suc i >? suc x
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | no ¬t | yes u = {!   !} -- fishy 
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var suc x} {var y}) | yes p | no ¬q | yes r | no ¬t | no ¬u = β-ƛ-∙
-- cong-shift {n} {i} n≥i (β-ƛ-∙ {var x} {var y}) | yes p | no ¬q | no ¬r = {!   !}
-- cong-shift {n} n≥i (β-ƛ-∙ {var x} {var y}) | no ¬p = {!   !}
-- cong-shift {n} n≥i (β-ƛ-∙ {var x} {ƛ N}) = {!   !}
-- cong-shift {n} n≥i (β-ƛ-∙ {var x} {N ∙ O}) = {!   !}
-- -- cong-shift {n} (β-ƛ-∙ {var x} {N}) with suc n >? x 
-- -- cong-shift {n} (β-ƛ-∙ {var zero} {N}) | yes p = β-ƛ-∙
-- -- cong-shift {n} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) with n >? suc x 
-- -- cong-shift {n} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | yes q = {!   !}
-- -- cong-shift {n} {i} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | no ¬q with suc i >? suc x 
-- -- cong-shift {n} {i} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | no ¬q | yes r = {!   !} -- fishy
-- -- cong-shift {n} {i} (β-ƛ-∙ {var suc x} {N}) | yes (s≤s p) | no ¬q | no ¬r = {!   !}
-- -- cong-shift {n} (β-ƛ-∙ {var zero} {var x}) | no ¬p = {!   !}
-- -- cong-shift {n} (β-ƛ-∙ {var zero} {ƛ N}) | no ¬p = {!   !}
-- -- cong-shift {n} (β-ƛ-∙ {var zero} {N ∙ O}) | no ¬p = {!   !}
-- -- cong-shift {n} (β-ƛ-∙ {var suc x} {N}) | no ¬p = {!   !}
-- cong-shift n≥i (β-ƛ-∙ {ƛ M} {N}) = {!   !}
-- cong-shift n≥i (β-ƛ-∙ {L ∙ var x} {N}) = {!   !}
-- cong-shift n≥i (β-ƛ-∙ {L ∙ (ƛ M)} {N}) = {!   !}
-- cong-shift n≥i (β-ƛ-∙ {L ∙ (M ∙ K)} {N}) = {!   !}
-- cong-shift n≥i (β-ƛ M→N) = β-ƛ (cong-shift _ M→N)
-- cong-shift n≥i (β-∙-l M→N) = β-∙-l (cong-shift _ M→N)
-- cong-shift n≥i (β-∙-r M→N) = β-∙-r (cong-shift _ M→N) 

-- -- cong-[] : ∀ {n i} {M N : Term n} → (L : Term (suc n)) → M β→ N → L [ M / i ] β→* L [ N / i ]
-- -- cong-[] {i = i} (var x) M→N with x ≟ i
-- -- cong-[] {i = i} (var x) M→N | yes p = hop M→N
-- -- cong-[] {i = i} (var x) M→N | no ¬p = ∎
-- -- cong-[] {n} {i} (ƛ L) M→N = {!   !}
-- --   -- cong-ƛ (cong-[] L (cong-shift M→N))
-- -- cong-[] {i = i} {M} {N} (L ∙ K) M→N =
-- --     L [ M / i ] ∙ K [ M / i ] 
-- --   →*⟨ cong-∙-l (cong-[] L M→N) ⟩ 
-- --     L [ N / i ] ∙ K [ M / i ] 
-- --   →*⟨ cong-∙-r (cong-[] K M→N) ⟩ 
-- --     L [ N / i ] ∙ K [ N / i ] 
-- --   →∎


-- cong-[]2 : ∀ {n i} {M N : Term n} → (L : Term (suc n)) → n ≥ i → M β→ N → L [ M / i ] β→* L [ N / i ]
-- cong-[]2 {n} {i} (var x) n≥i M→N with x ≟ i
-- cong-[]2 {n} {i} (var x) n≥i M→N | yes p = hop M→N
-- cong-[]2 {n} {i} (var x) n≥i M→N | no ¬p = ∎
-- cong-[]2 {n} {i} (ƛ M)   n≥i M→N = cong-ƛ (cong-[]2 M (s≤s n≥i) {! cong-shift  !})
-- cong-[]2 {n} {i} {M} {N} (L ∙ K) n≥i M→N =
--     L [ M / i ] ∙ K [ M / i ] 
--   →*⟨ cong-∙-l (cong-[]2 L _ M→N) ⟩ 
--     L [ N / i ] ∙ K [ M / i ] 
--   →*⟨ cong-∙-r (cong-[]2 K _ M→N) ⟩ 
--     L [ N / i ] ∙ K [ N / i ] 
--   →∎

-- β→confluent :  ∀ {n} (M N O : Term n) → (M β→ N) → (M β→ O) → ∃ (λ P → (N β→* P) × (O β→* P))
-- β→confluent .((ƛ M) ∙ N) _ _ (β-ƛ-∙ {M} {N}) β-ƛ-∙ = (M [ N ]) , (∎ , ∎)
-- β→confluent .((ƛ M) ∙ N) _ .(O ∙ N) (β-ƛ-∙ {M} {N}) (β-∙-l {N = O} M→O) = (O ∙ N) , ({!   !} , ∎)
-- β→confluent .((ƛ M) ∙ N) _ .((ƛ M) ∙ O) (β-ƛ-∙ {M} {N}) (β-∙-r {N = O} N→O) = (M [ O ]) , (cong-[]2 M z≤n N→O , (hop β-ƛ-∙))
-- β→confluent .(ƛ M) .(ƛ N) .(ƛ O) (β-ƛ {M} {N} M→N) (β-ƛ {N = O} M→O) with β→confluent M N O M→N M→O 
-- β→confluent .(ƛ M) .(ƛ N) .(ƛ O) (β-ƛ {M} {N} M→N) (β-ƛ {N = O} M→O) | P , N→P , O→P = (ƛ P) , ((cong-ƛ N→P) , (cong-ƛ O→P))
-- β→confluent .((ƛ M) ∙ L) .(N ∙ L) _ (β-∙-l {L} {N = N} M→N) (β-ƛ-∙ {M}) = (N ∙ L) , (∎ , {!   !})
-- β→confluent .(M ∙ L) .(N ∙ L) .(K ∙ L) (β-∙-l {L} {M} {N} M→N) (β-∙-l {N = K} M→O) with β→confluent M N K M→N M→O  
-- β→confluent .(M ∙ L) .(N ∙ L) .(K ∙ L) (β-∙-l {L} {M} {N} M→N) (β-∙-l {N = K} M→O) | P , N→P , K→P = P ∙ L , ((cong-∙-l N→P) , cong-∙-l K→P)
-- β→confluent .(M ∙ L) .(N ∙ L) .(M ∙ K) (β-∙-l {L} {M} {N} M→N) (β-∙-r {N = K} M→O) = N ∙ K , hop (β-∙-r M→O) , hop (β-∙-l M→N)
-- β→confluent .((ƛ L) ∙ M) .((ƛ L) ∙ N) _ (β-∙-r {M = M} {N} M→N) (β-ƛ-∙ {L}) = (L [ N ]) , (hop β-ƛ-∙ , cong-[]2 L _ M→N)
-- β→confluent .(K ∙ M) .(K ∙ N) .(L ∙ M) (β-∙-r {K} {M} {N} M→N) (β-∙-l {N = L} K→L) = (L ∙ N) , ((hop (β-∙-l K→L)) , hop (β-∙-r M→N))
-- β→confluent .(_ ∙ M) .(_ ∙ N) .(_ ∙ O) (β-∙-r {M = M} {N} M→N) (β-∙-r {N = O} M→O) with β→confluent M N O M→N M→O 
-- β→confluent .(L ∙ M) .(L ∙ N) .(L ∙ O) (β-∙-r {L} {M} {N} M→N) (β-∙-r {N = O} M→O) | P , N→P , O→P = (L ∙ P) , (cong-∙-r N→P , cong-∙-r O→P)

-- β→*-confluent :  ∀ {n} {M N O : Term n} → (M β→* N) → (M β→* O) → ∃ (λ P → (N β→* P) × (O β→* P))
-- β→*-confluent {n} {M} {.M} {O} ∎            M→O          = O , M→O , ∎
-- β→*-confluent {n} {M} {N} {.M} (M→L →* L→N) ∎            = N , ∎   , (M→L →* L→N)
-- β→*-confluent {n} {M} {N} {O}  (M→L →* L→N) (M→K →* K→O) = {!   !}



-- normal-unique : ∀ {n} {M N O : Term n} → Normal N → Normal O → M β→* N → M β→* O → N ≡ O
-- normal-unique P Q M→N M→O = let X = β→*-confluent M→N M→O in trans (normal P (proj₁ (proj₂ X))) (sym (normal Q (proj₂ (proj₂ X))))
