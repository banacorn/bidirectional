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

shift : (n i : ℕ) → Term → Term
shift free       i (ƛ M)        = ƛ shift (suc free) i M
shift free       i (M ∙ N)      = shift free i M ∙ shift free i N
shift zero       i (var x)      = var (x + i) -- every variables are deemed free regardless of its index
shift (suc free) i (var zero)   = var zero -- bound 
shift (suc free) i (var suc x)  = shift free (suc i) (var x)

-- infixl 10 _[_/_]
-- _[_/_] : Term → Term → ℕ → Term
-- (var x) [ N / i ] with compare x i 
-- ((var x) [ N / .(suc (x + k)) ])  | less .x k = var x
-- ((var x) [ N / .x ])              | equal .x = shift 0 x N
-- ((var .(suc (i + k))) [ N / i ])  | greater .i k = var (i + k)
-- (ƛ M)   [ N / i ] = ƛ (M [ N / suc i ])
-- (L ∙ M) [ N / i ] = L [ N / i ] ∙ M [ N / i ]

-- -- substitute the 0th var in M for N
-- infixl 10 _[_]
-- _[_] : Term → Term → Term
-- M [ N ] = M [ N / 0 ]


-- --------------------------------------------------------------------------------
-- -- relations


-- -- β-reduction
-- infix 3 _β→_
-- data _β→_ : Term → Term → Set where 

--   β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ (M [ N ])

--   β-ƛ : ∀ {M N} → M β→ N → ƛ M β→ ƛ N

--   β-∙-l : ∀ {L M N} → M β→ N → M ∙ L β→ N ∙ L

--   β-∙-r : ∀ {L M N} → M β→ N → L ∙ M β→ L ∙ N

-- open import Relation.Binary.Construct.Closure.ReflexiveTransitive 

-- infix  2 _β→*_ 
-- _β→*_ : Term → Term → Set
-- _β→*_ = Star _β→_
-- {-# DISPLAY Star _β→_ = _β→*_ #-}

-- module Example where

--   test-1 : ƛ (ƛ var 1) ∙ var 0 β→* ƛ var 0
--   test-1 = {!   !}


-- -- parallel β-reduction
-- infix 3 _β⇒_
-- data _β⇒_ : Term → Term → Set where 

--   β-var : {n : ℕ} → var n β⇒ var n

--   β-ƛ : ∀ {M M'} → (M⇒M' : M β⇒ M') → ƛ M β⇒ ƛ M'

--   β-∙ : ∀ {M M' N N'} → (M⇒M' : M β⇒ M') → (N⇒N' : N β⇒ N') → M ∙ N β⇒ M' ∙ N'

--   β-ƛ-∙ : ∀ {M M' N N'} → (M⇒M' : M β⇒ M') → (N⇒N' : N β⇒ N') → (ƛ M) ∙ N β⇒ M' [ N' ]

-- -- properties
-- β⇒identity : ∀ {M} → M β⇒ M
-- β⇒identity {var x} = β-var
-- β⇒identity {ƛ M}   = β-ƛ β⇒identity
-- β⇒identity {M ∙ N} = β-∙ β⇒identity β⇒identity

-- to-parallel : ∀ {M N} → M β→ N → M β⇒ N 
-- to-parallel β-ƛ-∙       = β-ƛ-∙ β⇒identity β⇒identity
-- to-parallel (β-ƛ M→N)   = β-ƛ (to-parallel M→N)
-- to-parallel (β-∙-l M→N) = β-∙ (to-parallel M→N) β⇒identity
-- to-parallel (β-∙-r M→N) = β-∙ β⇒identity (to-parallel M→N)

-- cong-ƛ : {M N : Term} → M β→* N → ƛ M β→* ƛ N
-- cong-ƛ = gmap _ β-ƛ

-- cong-∙-l : {L M N : Term} → M β→* N → M ∙ L β→* N ∙ L
-- cong-∙-l = gmap _ β-∙-l

-- cong-∙-r : {L M N : Term} → M β→* N → L ∙ M β→* L ∙ N
-- cong-∙-r = gmap _ β-∙-r 

-- cong-∙ : {M M' N N' : Term} → M β→* M' → N β→* N' → M ∙ N β→* M' ∙ N'
-- cong-∙ M→M' N→N' = (cong-∙-l M→M') ◅◅ (cong-∙-r N→N')

-- -- shift : (n i : ℕ) → Term → Term
-- -- shift free       i (ƛ M)        = ƛ shift (suc free) i M
-- -- shift free       i (M ∙ N)      = shift free i M ∙ shift free i N
-- -- shift zero       i (var x)      = var (x + i) -- every variables are deemed free regardless of its index
-- -- shift (suc free) i (var zero)   = var zero -- bound 
-- -- shift (suc free) i (var suc x)  = shift free i (var x)


-- -- cong-shift-app-var-0-var 0 (b+2) 1 0
-- -- shift (b+2) 0 (shift 0 1 (var 0)) β→* shift 0 1 (shift (b+2) 0 (var 0))

-- cong-shift-app-var-0-var : (a b i x : ℕ) → shift b 0 (shift a i (var x)) β→* shift a i (shift b 0 (var x))
-- cong-shift-app-var-0-var zero    zero    i x = {!   !}
-- cong-shift-app-var-0-var zero    (suc b) zero zero = ε
-- cong-shift-app-var-0-var zero    (suc zero) (suc i) zero = {!   !}
-- cong-shift-app-var-0-var zero    (suc (suc b)) (suc zero) zero = {!   !}
-- cong-shift-app-var-0-var zero    (suc (suc b)) (suc (suc i)) zero = {!   !}
-- cong-shift-app-var-0-var zero    (suc b) i (suc x) = {!   !}
-- cong-shift-app-var-0-var (suc a) zero    i x = {!   !}
-- cong-shift-app-var-0-var (suc a) (suc b) i x = {!   !}

-- cong-shift-app-var-0 : {a b i : ℕ} (N : Term) → shift b 0 (shift a i N) β→* shift a i (shift b 0 N)
-- cong-shift-app-var-0 {a} {b} {i} (var x) = cong-shift-app-var-0-var a b i x
-- cong-shift-app-var-0 (ƛ N)   = cong-ƛ (cong-shift-app-var-0 N)
-- cong-shift-app-var-0 (M ∙ N) = cong-∙ (cong-shift-app-var-0 M) (cong-shift-app-var-0 N)


-- cong-shift-app-var : {free i : ℕ} (x : ℕ) (N : Term) → shift (suc free) i (var x) [ shift free i N ] β→* shift free i ((var x) [ N ])
-- cong-shift-app-var {free} {i} zero N = cong-shift-app-var-0 N
-- cong-shift-app-var {free} {i} (suc x) N = {!   !}

-- cong-shift-app : {free i : ℕ} (M N : Term) → shift free i ((ƛ M) ∙ N) β→* shift free i (M [ N ])
-- cong-shift-app (var x) N = β-ƛ-∙ ◅ cong-shift-app-var x N
-- cong-shift-app (ƛ M)   N = {!   !}
-- cong-shift-app (K ∙ M) N = {!   !}

-- cong-shift : {free i : ℕ} {M N : Term} → M β→ N → shift free i M β→* shift free i N
-- cong-shift (β-ƛ M→N)        = cong-ƛ (cong-shift M→N)
-- cong-shift (β-ƛ-∙ {M} {N})  = cong-shift-app M N
-- cong-shift (β-∙-l M→N)      = cong-∙-l (cong-shift M→N)
-- cong-shift (β-∙-r M→N)      = cong-∙-r (cong-shift M→N)

-- -- cong-shift : {free i : ℕ} {M N : Term} → M β→ N → shift free i M β→* shift free i N
-- -- cong-shift (β-ƛ M→N)   = cong-ƛ (cong-shift M→N)
-- -- cong-shift (β-ƛ-∙ {M} {N}) = cong-shift-app M N
-- -- cong-shift (β-∙-l M→N) = cong-∙-l (cong-shift M→N)
-- -- cong-shift (β-∙-r M→N) = cong-∙-r (cong-shift M→N)


-- -- cong-[]-r : ∀ L {M N i} → M β→ N → L [ M / i ] β→* L [ N / i ]
-- -- cong-[]-r (var x) {M} {N} {i} M→N with compare x i 
-- -- cong-[]-r (var x) {M} {N} {.(suc (x + k))}  M→N | less .x k = ε
-- -- cong-[]-r (var x) {M} {N} {.x}              M→N | equal .x = cong-shift M→N
-- -- cong-[]-r (var .(suc (m + k))) {M} {N} {.m} M→N | greater m k = ε
-- -- cong-[]-r (ƛ L)   M→N = cong-ƛ (cong-[]-r L M→N)
-- -- cong-[]-r (K ∙ L) M→N = cong-∙-l (cong-[]-r K M→N) ◅◅ cong-∙-r (cong-[]-r L M→N)


-- -- cong-[]-l : ∀ {M N L i} → M β→ N → M [ L / i ] β→* N [ L / i ]
-- -- cong-[]-l {ƛ M}                 (β-ƛ M→N)   = cong-ƛ   (cong-[]-l M→N)
-- -- cong-[]-l {.(ƛ K) ∙ M} {L = L}  (β-ƛ-∙ {K}) = {!   !}
-- -- cong-[]-l {K ∙ M}               (β-∙-l M→N) = cong-∙-l (cong-[]-l M→N)
-- -- cong-[]-l {K ∙ M}               (β-∙-r M→N) = cong-∙-r (cong-[]-l M→N)



-- -- cong-[] : {M M' N N' : Term} → M β→* M' → N β→* N' → M [ N ] β→* M' [ N' ]
-- -- cong-[] {M} ε            ε            = ε
-- -- cong-[] {M} {N = L} {N'} ε (_◅_ {j = N} L→N N→N') = M[L]→M[N] ◅◅ M[N]→M[N']
-- --     where 
-- --         M[L]→M[N] : M [ L ] β→* M [ N ]
-- --         M[L]→M[N] = cong-[]-r M L→N

-- --         M[N]→M[N'] : M [ N ] β→* M [ N' ]
-- --         M[N]→M[N'] = cong-[] {M} ε N→N'
-- -- cong-[] {M} (K→M ◅ M→M') N→N' = cong-[]-l K→M ◅◅ cong-[] M→M' N→N'

-- -- from-parallel : ∀ {M N} → M β⇒ N → M β→* N
-- -- from-parallel β-var             = ε
-- -- from-parallel (β-ƛ M⇒N)         = cong-ƛ (from-parallel M⇒N)
-- -- from-parallel (β-∙ M⇒M' N⇒N')   = cong-∙ (from-parallel M⇒M') (from-parallel N⇒N')
-- -- from-parallel (β-ƛ-∙ M⇒M' N⇒N') = return β-ƛ-∙ ◅◅ cong-[] (from-parallel M⇒M') (from-parallel N⇒N') 

