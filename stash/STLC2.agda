module STLC2 where 


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
data Term : Set where
  var_ : ℕ → Term 

  ƛ_ : Term → Term 

  _∙_ : Term → Term → Term 


-- only "shift" the variable when 
--  1. it's free
--  2. it will be captured after substitution
--  free <= x && x < subst-depth
shift : ℕ → ℕ → Term → Term 
shift free subst-depth (var x) with free >? x
shift free subst-depth (var x) | yes p = var x                -- bound 
shift free subst-depth (var x) | no ¬p with subst-depth >? x  -- free 
shift free subst-depth (var x) | no ¬p | yes q = var (suc x)  -- will be captured, should increment
shift free subst-depth (var x) | no ¬p | no ¬q = var x        
shift free subst-depth (ƛ M)   = ƛ (shift (suc free) (suc subst-depth) M)
shift free subst-depth (M ∙ N) = shift free subst-depth M ∙ shift free subst-depth N


infixl 10 _[_/_]
_[_/_] : Term → Term → ℕ → Term 
(var x)   [ N / n ] with x ≟ n 
(var x)   [ N / n ] | yes p = N
(var x)   [ N / n ] | no ¬p = var x
(ƛ M)     [ N / n ] = ƛ ((M [ shift 0 (suc n) N / suc n ]))
(L ∙ M)   [ N / n ] = L [ N / n ] ∙ M [ N / n ]

-- substitution
infixl 10 _[_]
_[_] : Term → Term → Term 
M [ N ] = M [ N / zero ]

-- β reduction
infix 3 _β→_
data _β→_ : Term → Term → Set where 

  β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ (M [ N ])

  β-ƛ : ∀ {M N} → M β→ N → ƛ M β→ ƛ N

  β-∙-l : ∀ {L M N} → M β→ N → M ∙ L β→ N ∙ L

  β-∙-r : ∀ {L M N} → M β→ N → L ∙ M β→ L ∙ N



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


infixl  3 _<β>_ 
_<β>_ : ∀ {M N O} → M β→* N → N β→* O → M β→* O
_<β>_ {M} {.M} {O} ∎            N→O = N→O
_<β>_ {M} {N}  {O} (L→M →* M→N) N→O = L→M →* M→N <β> N→O



-- infix  2 _-↠_ 

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


jump : ∀ {M N} → M β→ N → M β→* N
jump {M} {N} M→N = M→N →* ∎

-- the symmetric closure of _β→*_

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

-- data Normal : Set where 

Normal : Term → Set 
Normal M = ¬ ∃ (λ N → M β→ N)

normal : ∀ {M N} → Normal M → M β→* N → M ≡ N 
normal P ∎            = refl
normal P (M→L →* L→N) = ⊥-elim (P (_ , M→L))

normal-ƛ : ∀ {M} → Normal (ƛ M) → Normal M
normal-ƛ P (N , M→N) = P ((ƛ N) , (β-ƛ M→N))

normal-ƛ' : ∀ {M} → Normal M → Normal (ƛ M)
normal-ƛ' P (.(ƛ N) , β-ƛ {N = N} ƛM→N) = P (N , ƛM→N)

normal-∙-r : ∀ {M N} → Normal (M ∙ N) → Normal N
normal-∙-r {M} P (O , N→O) = P (M ∙ O , (β-∙-r N→O))

normal-∙-l : ∀ {M N} → Normal (M ∙ N) → Normal M
normal-∙-l {_} {N} P (O , M→O) = P (O ∙ N , (β-∙-l M→O))


cong-ƛ : ∀ {M N} → M β→* N → ƛ M β→* ƛ N
cong-ƛ ∎            = ∎
cong-ƛ (M→N →* N→O) = β-ƛ M→N →* cong-ƛ N→O


cong-∙-l : ∀ {L M N} → M β→* N → M ∙ L β→* N ∙ L
cong-∙-l ∎            = ∎
cong-∙-l (M→N →* N→O) = β-∙-l M→N →* cong-∙-l N→O


cong-∙-r : ∀ {L M N} → M β→* N → L ∙ M β→* L ∙ N
cong-∙-r ∎            = ∎
cong-∙-r (M→N →* N→O) = β-∙-r M→N →* cong-∙-r N→O

∙-dist-r : ∀ M N O → (ƛ (M ∙ N)) ∙ O β→* ((ƛ M) ∙ O) ∙ ((ƛ N) ∙ O) 
∙-dist-r (var x) N O = {!   !}
∙-dist-r (ƛ M) N O = {!   !}
∙-dist-r (M ∙ L) N O = {!   !}

∙-dist-r2 : ∀ M N O → (ƛ (M ∙ N)) ∙ O β≡ ((ƛ M) ∙ O) ∙ ((ƛ N) ∙ O) 
∙-dist-r2 (var x) N O = {!   !}
∙-dist-r2 (ƛ M) N O = {!   !}
∙-dist-r2 (M ∙ L) (var x) O = 
    (ƛ (M ∙ L ∙ var x)) ∙ O 
  =*⟨ β-sym (β-ƛ-∙ →* ∎) {!   !} ⟩ 
    ((M ∙ L ∙ var x) [ O ])
  =*⟨ {!   !} ⟩ 
    {!   !} 
  =*⟨ {!   !} ⟩ 
    (ƛ M ∙ L) ∙ O ∙ ((ƛ var x) ∙ O) 
  =∎
∙-dist-r2 (M ∙ L) (ƛ N) O = {!   !}
∙-dist-r2 (M ∙ L) (N ∙ K) O = {!   !}

  --   {!   !}
  -- →*⟨ {!   !} ⟩ 
  --   {!   !}
  -- →*⟨ {!   !} ⟩ 
  --   {!   !}
  -- →*⟨ {!   !} ⟩ 
  --   {!   !}
  -- →*⟨ {!   !} ⟩ 
  --   {!   !}
  -- →∎

-- (ƛ M)     [ N / n ] = ƛ ((M [ shift 0 (suc n) N / suc n ]))

cong-[]2 : ∀ {M N L n} → M β→ N → (M [ L / n ]) β→* (N [ L / n ])
cong-[]2 (β-ƛ-∙ {var x} {N}) = {!   !}
cong-[]2 {_} {_} {L} {n} (β-ƛ-∙ {ƛ M} {N}) =
    (ƛ (ƛ (M [ shift 0 (suc (suc n)) (shift 0 (suc n) L) / suc (suc n) ]))) ∙ (N [ L / n ]) 
  →*⟨ jump β-ƛ-∙ ⟩ 
    ƛ ((M [ shift 0 (suc (suc n)) (shift 0 (suc n) L) / suc (suc n) ]) [ shift 0 1 (N [ L / n ]) / 1 ]) 
  →*⟨  cong-ƛ {!  !} ⟩ 
    ƛ {!   !}
  →*⟨ {!   !} ⟩ 
    {!   !} 
  →*⟨ {!   !} ⟩ 
    ƛ ((M [ shift 0 1 N / 1 ]) [ shift 0 (suc n) L / suc n ])
  →∎
cong-[]2 {_} {_} {L} {n} (β-ƛ-∙ {M ∙ K} {N}) = 
    (ƛ (M [ shift 0 (suc n) L / suc n ]) ∙ (K [ shift 0 (suc n) L / suc n ])) ∙ (N [ L / n ])
  →*⟨ {!   !} ⟩ 
  -- →*⟨ forward (∙-dist-r2 (M [ shift zero (suc n) L / suc n ]) (K [ shift zero (suc n) L / suc n ]) (N [ L / n ])) ⟩ 
    (ƛ (M [ shift zero (suc n) L / suc n ])) ∙ (N [ L / n ]) ∙ ((ƛ (K [ shift 0 (suc n) L / suc n ])) ∙ (N [ L / n ])) 
  →*⟨ cong-∙-l (cong-[]2 (β-ƛ-∙ {M} {N})) ⟩ 
    ((M [ N ]) [ L / n ]) ∙ ((ƛ (K [ shift 0 (suc n) L / suc n ])) ∙ (N [ L / n ])) 
  →*⟨ cong-∙-r (cong-[]2 (β-ƛ-∙ {K} {N})) ⟩ 
    ((M [ N ]) [ L / n ]) ∙ ((K [ N ]) [ L / n ])
  →∎
cong-[]2 (β-ƛ M→N) = cong-ƛ (cong-[]2 M→N)
cong-[]2 (β-∙-l M→N) = cong-∙-l (cong-[]2 M→N)
cong-[]2 (β-∙-r M→N) = cong-∙-r (cong-[]2 M→N)


cong-∙-l' : ∀ {L M N} → M β→* N → M ∙ L ≡ N ∙ L
cong-∙-l' ∎                = refl
cong-∙-l' {L} {M} {O} (_→*_ {M = N} M→N N→O) = trans M∙L≡N∙L N∙L≡O∙L
  where
    M∙L≡N∙L : M ∙ L ≡ N ∙ L
    M∙L≡N∙L = {!   !}

    N∙L≡O∙L : N ∙ L ≡ O ∙ L
    N∙L≡O∙L = cong-∙-l' N→O
  -- rans (cong-∙-l' (M→N →* ∎)) (cong-∙-l' N→O)


cong-[] : ∀ {M N L n} → M β→ N → (M [ L / n ]) ≡ (N [ L / n ])
cong-[] β-ƛ-∙ = {!   !}
cong-[] (β-ƛ M→N) = {!   !}
cong-[] (β-∙-l M→N) = cong-∙-l' {! cong-[] M→N  !}
cong-[] (β-∙-r M→N) = {!   !}

normal-unique' : ∀ {M N O} → Normal N → Normal O → M β→ N → M β→ O → N ≡ O
normal-unique' P Q β-ƛ-∙ β-ƛ-∙ = refl
normal-unique' P Q (β-ƛ-∙ {M} {L}) (β-∙-l {N = .(ƛ N)} (β-ƛ {N = N} M→N)) = {!   !}
  -- trans (normal P (cong-[]2 M→N)) N[L]≡ƛN∙L
  -- trans (normal P (cong-[]2 M→N)) N[L]≡ƛN∙L 
  where 
    N[L]≡ƛN∙L : (N [ L ]) ≡ (ƛ N) ∙ L
    N[L]≡ƛN∙L = sym (normal Q (jump β-ƛ-∙))
-- β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ (M [ N ])
normal-unique' P Q (β-ƛ-∙ {M} {L}) (β-∙-r {N = N} L→N) = {!  sym (normal Q (jump β-ƛ-∙)) !}
  -- sym (trans (normal Q (jump β-ƛ-∙)) (cong (λ x → M [ x ]) (sym (normal {!   !} (jump N→O)))))
  -- sym (trans (normal Q (jump β-ƛ-∙)) (cong (λ x → {! M [ x ]  !}) {!   !}))
  -- sym (trans {!   !} (normal {! P  !} (jump β-ƛ-∙)))
normal-unique' P Q (β-ƛ M→N) (β-ƛ M→O) = cong ƛ_ (normal-unique' (normal-ƛ P) (normal-ƛ Q) M→N M→O)
normal-unique' P Q (β-∙-l M→N) β-ƛ-∙ = {!normal (normal-∙-l P) !}
normal-unique' P Q (β-∙-l {L} {N = N} M→N) (β-∙-l {N = O} M→O) = 
  cong (λ x → x ∙ L) (normal-unique' (normal-∙-l P) (normal-∙-l Q) M→N M→O)
normal-unique' P Q (β-∙-l M→N) (β-∙-r M→O) = 
  cong₂ _∙_ (sym (normal (normal-∙-l Q) (jump M→N))) (normal (normal-∙-r P) (jump M→O))
normal-unique' {O = O} P Q (β-∙-r {L} {N = N} M→N) M→O =
  {!   !}

normal-unique : ∀ {M N O} → Normal N → Normal O → M β→* N → M β→* O → N ≡ O
normal-unique P Q ∎            M→O          = normal P M→O
normal-unique P Q M→N          ∎            = sym (normal Q M→N)
normal-unique P Q (_→*_ {M = L} M→L L→N) (_→*_ {M = K} M→K K→O) = {!   !}
  -- rewrite (normal-unique' {!   !} {!   !} M→L M→K) = normal-unique P Q L→N {!  K→O !}
  -- where 
  --   postulate L≡K : L ≡ K 
  -- normal-unique' P Q {!   !} {!   !}
-- ... | U = {!   !}
  -- trans {!   !} (normal-unique {!   !} {!   !} L→N {!   !})
    -- L≡K = {!   !}
  -- normal-unique P Q {!   !} M→O
-- normal-unique P Q M→N ∎            = sym (normal Q M→N)
-- normal-unique P Q M→N (M→L →* L→O) = {!   !}

-- β→*-confluent : ∀ {M N O} → (M β→* N) → (M β→* O) → ∃ (λ P → (N β→* P) × (O β→* P))
-- β→*-confluent {M} {.M} {O} ∎            M→O          = O , M→O , ∎
-- β→*-confluent {M} {N} {.M} (M→L →* L→N) ∎            = N , ∎   , (M→L →* L→N)
-- β→*-confluent {M} {N} {O}  (M→L →* L→N) (M→K →* K→O) = {!   !}


-- lemma-0 : ∀ M N → M [ N ] β→* (ƛ M) ∙ N 
-- lemma-0 (var zero) (var zero) = (var zero) →⟨ {!   !} ⟩ {!   !}
-- lemma-0 (var zero) (var suc y) = {!   !}
-- lemma-0 (var suc x) (var y) = {!   !}
-- lemma-0 (var x) (ƛ O) = {!   !}
-- lemma-0 (var x) (O ∙ P) = {!   !}
-- lemma-0 (ƛ M)   O = {!   !}
-- lemma-0 (M ∙ N) O = {!   !}


-- lemma : ∀ M N O → ((ƛ M) ∙ N β→* O) → M [ N ] β→* O
-- lemma (var x) N .((ƛ var x) ∙ N) (.((ƛ var x) ∙ N) ∎) = {!   !}
-- lemma (ƛ M) N .((ƛ (ƛ M)) ∙ N) (.((ƛ (ƛ M)) ∙ N) ∎) = {!   !}
-- lemma (M ∙ M₁) N .((ƛ M ∙ M₁) ∙ N) (.((ƛ M ∙ M₁) ∙ N) ∎) = {!   !}
-- lemma M N O (.((ƛ M) ∙ N) →⟨⟩ redex→O) = lemma M N O redex→O
-- lemma M N O (_→⟨_⟩_ .((ƛ M) ∙ N) {P} ƛM∙N→P P→O) = {!   !}
-- -- lemma M N P (jump ƛM∙N→P) <β> P→O


-- lemma-1 : ∀ M N O P → (ƛ M β→* N) → (N ∙ O β→* P) → M [ O ] β→* P 
-- lemma-1 M .(ƛ M) O P (.(ƛ M) ∎)           N∙O→P = lemma M O P N∙O→P
-- lemma-1 M N      O P (.(ƛ M) →⟨⟩ ƛM→N)    N∙O→P = lemma-1 M N O P ƛM→N N∙O→P
-- lemma-1 M N O .(N ∙ O) (.(ƛ M) →⟨ x ⟩ ƛM→N) (.(N ∙ O) ∎) = {!   !}
-- lemma-1 M N O P (.(ƛ M) →⟨ x ⟩ ƛM→N) (.(N ∙ O) →⟨⟩ N∙O→P) = {!   !}
-- lemma-1 M N O P (.(ƛ M) →⟨ x ⟩ ƛM→N) (.(N ∙ O) →⟨ x₁ ⟩ N∙O→P) = {!   !}

-- -- (M [ N ]) β→* O
-- -- M'→O : P ∙ N β→* O
-- -- L→M' : ƛ M β→ P
-- -- (M [ N ]) β→* O

-- -- M'→O : N₂ ∙ N β→* O

-- -- L→M' : ƛ M β→ N₂

-- -- M→N : (M [ N ]) β→* N₁

-- -- that diamond prop
-- --      
-- --      M 
-- --   N     O
-- --      P
-- --
-- β→*-confluent : ∀ {M N O} → (M β→* N) → (M β→* O) → ∃ (λ P → (N β→* P) × (O β→* P))
-- β→*-confluent {O = O} (M ∎)            M→O                 = O , M→O , (O ∎)
-- β→*-confluent         (L →⟨⟩ M→N)      M→O                 = β→*-confluent M→N M→O
-- β→*-confluent {N = N} (L →⟨ x ⟩ M→N)   (.L ∎)              = N , (N ∎) , (L →⟨ x ⟩ M→N)
-- β→*-confluent         (L →⟨ x ⟩ M→N)   (.L →⟨⟩ M→O)        = β→*-confluent (L →⟨ x ⟩ M→N) M→O
-- β→*-confluent (.((ƛ _) ∙ _) →⟨ β-ƛ-∙ ⟩ M→N) (.((ƛ _) ∙ _) →⟨ β-ƛ-∙ ⟩ M'→O) = β→*-confluent M→N M'→O
-- β→*-confluent {N = N} {O} (.((ƛ M) ∙ N₁) →⟨ β-ƛ-∙ {M} {N₁} ⟩ M→N) (.((ƛ M) ∙ N₁) →⟨ β-∙-l {N = N₂} L→M' ⟩ M'→O) = β→*-confluent M→N (lemma-1 M N₂ N₁ O ((ƛ M) →⟨ L→M' ⟩ (N₂ ∎)) M'→O)
-- β→*-confluent (.((ƛ _) ∙ _) →⟨ β-ƛ-∙ ⟩ M→N) (.((ƛ _) ∙ _) →⟨ β-∙-r L→M' ⟩ M'→O) = {!   !}
-- β→*-confluent (.(ƛ _) →⟨ β-ƛ L→M ⟩ M→N) (.(ƛ _) →⟨ L→M' ⟩ M'→O) = {!   !}
-- β→*-confluent (.(_ ∙ _) →⟨ β-∙-l L→M ⟩ M→N) (.(_ ∙ _) →⟨ L→M' ⟩ M'→O) = {!   !}
-- β→*-confluent (.(_ ∙ _) →⟨ β-∙-r L→M ⟩ M→N) (.(_ ∙ _) →⟨ L→M' ⟩ M'→O) = {!   !}

--       L
--     M   M' 
--   N       O
--       P
--

-- module Example where 

--   S : Term 
--   S = ƛ ƛ ƛ var 2 ∙ var 0 ∙ (var 1 ∙ var 0)

--   K : Term 
--   K = ƛ ƛ var 1

--   I : Term 
--   I = ƛ (var 0)

--   Z : Term 
--   Z = ƛ ƛ var 0

--   SZ : Term 
--   SZ = ƛ ƛ var 1 ∙ var 0

--   PLUS : Term 
--   PLUS = ƛ ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)

--   test-0 : ƛ (ƛ ƛ var 1) ∙ var 0 β→* ƛ ƛ var 1
--   test-0 = 
--       ƛ (ƛ ƛ var 1) ∙ var 0
--     →⟨ β-ƛ β-ƛ-∙ ⟩ 
--       ƛ (ƛ var 1) [ var 0 / 0 ]
--     →⟨⟩ 
--       ƛ ƛ ((var 1) [ shift 0 1 (var 0) / 1 ])
--     →⟨⟩ 
--       ƛ ƛ ((var 1) [ var 1 / 1 ])
--     →⟨⟩ 
--       ƛ (ƛ var 1)
--     ∎


--   test-2 : PLUS ∙ Z ∙ SZ β→* SZ
--   test-2 = 
--       PLUS ∙ Z ∙ SZ
--     →⟨⟩ 
--       (ƛ (ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero))))) ∙ Z ∙ SZ
--     →⟨ β-∙-l β-ƛ-∙ ⟩ 
--       ((ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)))) [ Z ]) ∙ SZ
--     →⟨⟩ 
--       ((ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)))) [ Z / 0 ]) ∙ SZ
--     →⟨⟩
--       (ƛ ((ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero))) [ shift 0 1 Z / 1 ])) ∙ SZ
--     →⟨⟩
--       (ƛ ((ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero))) [ Z / 1 ])) ∙ SZ
--     →⟨⟩
--       (ƛ (ƛ ((ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ Z / 2 ]))) ∙ SZ
--     →⟨⟩
--       (ƛ (ƛ (ƛ ((var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ Z / 3 ])))) ∙ SZ
--     →⟨⟩
--       (ƛ ƛ ƛ Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) ∙ SZ
--     →⟨ β-ƛ-∙ ⟩ 
--       ((ƛ ƛ Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ SZ / 0 ])
--     →⟨⟩
--       ƛ ((ƛ Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ SZ / 1 ])
--     →⟨⟩
--       ƛ ƛ ((Z ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ SZ / 2 ])
--     →⟨⟩
--       ƛ ƛ Z ∙ var 1 ∙ (SZ ∙ var 1 ∙ var 0)
--     →⟨ β-ƛ (β-ƛ (β-∙-r (β-∙-l β-ƛ-∙))) ⟩ 
--       ƛ ƛ Z ∙ var 1 ∙ (((ƛ var 1 ∙ var 0) [ var 1 ]) ∙ var 0)
--     →⟨⟩
--       ƛ ƛ Z ∙ var 1 ∙ (((ƛ var 1 ∙ var 0) [ var 1 / 0 ]) ∙ var 0)
--     →⟨⟩
--       ƛ ƛ Z ∙ var 1 ∙ ((ƛ ((var 1 ∙ var 0) [ shift 0 1 (var 1) / 1 ])) ∙ var 0)
--     →⟨⟩
--       ƛ ƛ Z ∙ var 1 ∙ ((ƛ ((var 1 ∙ var 0) [ var 1 / 1 ])) ∙ var 0)
--     →⟨⟩
--       ƛ ƛ Z ∙ var 1 ∙ ((ƛ var 1 ∙ var 0) ∙ var 0)
--     →⟨ β-ƛ (β-ƛ (β-∙-r β-ƛ-∙)) ⟩ 
--       ƛ ƛ Z ∙ var 1 ∙ ((var 1 ∙ var 0) [ var 0 / 0 ])
--     →⟨⟩
--       ƛ ƛ (ƛ ƛ var 0) ∙ var 1 ∙ (var 1 ∙ var 0)
--     →⟨ β-ƛ (β-ƛ (β-∙-l β-ƛ-∙)) ⟩ 
--       ƛ ƛ ((ƛ var 0) [ var 1 / 0 ]) ∙ (var 1 ∙ var 0)
--     →⟨⟩ 
--       ƛ ƛ (ƛ ((var 0) [ var 1 / 1 ])) ∙ (var 1 ∙ var 0)
--     →⟨⟩ 
--       ƛ ƛ (ƛ var 0) ∙ (var 1 ∙ var 0)
--     →⟨ β-ƛ (β-ƛ β-ƛ-∙) ⟩ 
--       ƛ ƛ ((var 0) [ var 1 ∙ var 0 / 0 ])
--     →⟨⟩ 
--       SZ 
--     ∎