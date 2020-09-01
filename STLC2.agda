module STLC2 where 


open import Data.Nat
-- open import Data.List
-- open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_)
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

_[_/_] : Term → Term → ℕ → Term 
(var x)   [ N / n ] with x ≟ n 
(var x)   [ N / n ] | yes p = N
(var x)   [ N / n ] | no ¬p = var x
(ƛ M)     [ N / n ] = ƛ ((M [ shift 0 (suc n) N / suc n ]))
(L ∙ M)   [ N / n ] = L [ N / n ] ∙ M [ N / n ]

-- substitution
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
infixr 2 _→⟨_⟩_
infixr 2 _→⟨⟩_
infix 3 _∎
data _β→*_ : Term → Term → Set where
  _∎ : ∀ M → M β→* M 

  _→⟨⟩_
    : ∀ L {M}          
    → L β→* M
    --------------
    → L β→* M
    
  _→⟨_⟩_
    : ∀ L {M N}          
    → L β→ M       
    → M β→* N       
    --------------
    → L β→* N

jump : ∀ {M N} → M β→ N → M β→* N
jump {M} {N} M→N = M →⟨ M→N ⟩ N ∎

infixl  3 _<β>_ 
_<β>_ : ∀ {M N O} → M β→* N → N β→* O → M β→* O
_<β>_ {M} {.M} {O} (M ∎) N→O = N→O
_<β>_ {.L} {N} {O} (L →⟨⟩ M→N) N→O = M→N <β> N→O
_<β>_ {.L} {N} {O} (L →⟨ x ⟩ M→N) N→O = L →⟨ x ⟩ M→N <β> N→O


 

-- the symmetric closure of _β→*_
infix  1 _β≡_ 
data _β≡_ : Term → Term → Set where
  sym : ∀ {M N}
    → M β→* N
    → N β→* M
    -------
    → M β≡ N


-- lemma-0 : ∀ M N → M [ N ] β→* (ƛ M) ∙ N 
-- lemma-0 (var zero) (var zero) = (var zero) →⟨ {!   !} ⟩ {!   !}
-- lemma-0 (var zero) (var suc y) = {!   !}
-- lemma-0 (var suc x) (var y) = {!   !}
-- lemma-0 (var x) (ƛ O) = {!   !}
-- lemma-0 (var x) (O ∙ P) = {!   !}
-- lemma-0 (ƛ M)   O = {!   !}
-- lemma-0 (M ∙ N) O = {!   !}


lemma : ∀ M N O → ((ƛ M) ∙ N β→* O) → M [ N ] β→* O
lemma (var x) N .((ƛ var x) ∙ N) (.((ƛ var x) ∙ N) ∎) = {!   !}
lemma (ƛ M) N .((ƛ (ƛ M)) ∙ N) (.((ƛ (ƛ M)) ∙ N) ∎) = {!   !}
lemma (M ∙ M₁) N .((ƛ M ∙ M₁) ∙ N) (.((ƛ M ∙ M₁) ∙ N) ∎) = {!   !}
lemma M N O (.((ƛ M) ∙ N) →⟨⟩ redex→O) = lemma M N O redex→O
lemma M N O (_→⟨_⟩_ .((ƛ M) ∙ N) {P} ƛM∙N→P P→O) = {!   !}
-- lemma M N P (jump ƛM∙N→P) <β> P→O


lemma-1 : ∀ M N O P → (ƛ M β→* N) → (N ∙ O β→* P) → M [ O ] β→* P 
lemma-1 M .(ƛ M) O P (.(ƛ M) ∎)           N∙O→P = lemma M O P N∙O→P
lemma-1 M N      O P (.(ƛ M) →⟨⟩ ƛM→N)    N∙O→P = lemma-1 M N O P ƛM→N N∙O→P
lemma-1 M N O .(N ∙ O) (.(ƛ M) →⟨ x ⟩ ƛM→N) (.(N ∙ O) ∎) = {!   !}
lemma-1 M N O P (.(ƛ M) →⟨ x ⟩ ƛM→N) (.(N ∙ O) →⟨⟩ N∙O→P) = {!   !}
lemma-1 M N O P (.(ƛ M) →⟨ x ⟩ ƛM→N) (.(N ∙ O) →⟨ x₁ ⟩ N∙O→P) = {!   !}

-- (M [ N ]) β→* O
-- M'→O : P ∙ N β→* O
-- L→M' : ƛ M β→ P
-- (M [ N ]) β→* O

-- M'→O : N₂ ∙ N β→* O

-- L→M' : ƛ M β→ N₂

-- M→N : (M [ N ]) β→* N₁

-- that diamond prop
--      
--      M 
--   N     O
--      P
--
β→*-confluent : ∀ {M N O} → (M β→* N) → (M β→* O) → ∃ (λ P → (N β→* P) × (O β→* P))
β→*-confluent {O = O} (M ∎)            M→O                 = O , M→O , (O ∎)
β→*-confluent         (L →⟨⟩ M→N)      M→O                 = β→*-confluent M→N M→O
β→*-confluent {N = N} (L →⟨ x ⟩ M→N)   (.L ∎)              = N , (N ∎) , (L →⟨ x ⟩ M→N)
β→*-confluent         (L →⟨ x ⟩ M→N)   (.L →⟨⟩ M→O)        = β→*-confluent (L →⟨ x ⟩ M→N) M→O
β→*-confluent (.((ƛ _) ∙ _) →⟨ β-ƛ-∙ ⟩ M→N) (.((ƛ _) ∙ _) →⟨ β-ƛ-∙ ⟩ M'→O) = β→*-confluent M→N M'→O
β→*-confluent {N = N} {O} (.((ƛ M) ∙ N₁) →⟨ β-ƛ-∙ {M} {N₁} ⟩ M→N) (.((ƛ M) ∙ N₁) →⟨ β-∙-l {N = N₂} L→M' ⟩ M'→O) = β→*-confluent M→N (lemma-1 M N₂ N₁ O ((ƛ M) →⟨ L→M' ⟩ (N₂ ∎)) M'→O)
β→*-confluent (.((ƛ _) ∙ _) →⟨ β-ƛ-∙ ⟩ M→N) (.((ƛ _) ∙ _) →⟨ β-∙-r L→M' ⟩ M'→O) = {!   !}
β→*-confluent (.(ƛ _) →⟨ β-ƛ L→M ⟩ M→N) (.(ƛ _) →⟨ L→M' ⟩ M'→O) = {!   !}
β→*-confluent (.(_ ∙ _) →⟨ β-∙-l L→M ⟩ M→N) (.(_ ∙ _) →⟨ L→M' ⟩ M'→O) = {!   !}
β→*-confluent (.(_ ∙ _) →⟨ β-∙-r L→M ⟩ M→N) (.(_ ∙ _) →⟨ L→M' ⟩ M'→O) = {!   !}

--       L
--     M   M' 
--   N       O
--       P
--

module Example where 

  S : Term 
  S = ƛ ƛ ƛ var 2 ∙ var 0 ∙ (var 1 ∙ var 0)

  K : Term 
  K = ƛ ƛ var 1

  I : Term 
  I = ƛ (var 0)

  Z : Term 
  Z = ƛ ƛ var 0

  SZ : Term 
  SZ = ƛ ƛ var 1 ∙ var 0

  PLUS : Term 
  PLUS = ƛ ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)

  test-0 : ƛ (ƛ ƛ var 1) ∙ var 0 β→* ƛ ƛ var 1
  test-0 = 
      ƛ (ƛ ƛ var 1) ∙ var 0
    →⟨ β-ƛ β-ƛ-∙ ⟩ 
      ƛ (ƛ var 1) [ var 0 / 0 ]
    →⟨⟩ 
      ƛ ƛ ((var 1) [ shift 0 1 (var 0) / 1 ])
    →⟨⟩ 
      ƛ ƛ ((var 1) [ var 1 / 1 ])
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
      (ƛ ((ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero))) [ shift 0 1 Z / 1 ])) ∙ SZ
    →⟨⟩
      (ƛ ((ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero))) [ Z / 1 ])) ∙ SZ
    →⟨⟩
      (ƛ (ƛ ((ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ Z / 2 ]))) ∙ SZ
    →⟨⟩
      (ƛ (ƛ (ƛ ((var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var zero)) [ Z / 3 ])))) ∙ SZ
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
      ƛ ƛ Z ∙ var 1 ∙ (((ƛ var 1 ∙ var 0) [ var 1 ]) ∙ var 0)
    →⟨⟩
      ƛ ƛ Z ∙ var 1 ∙ (((ƛ var 1 ∙ var 0) [ var 1 / 0 ]) ∙ var 0)
    →⟨⟩
      ƛ ƛ Z ∙ var 1 ∙ ((ƛ ((var 1 ∙ var 0) [ shift 0 1 (var 1) / 1 ])) ∙ var 0)
    →⟨⟩
      ƛ ƛ Z ∙ var 1 ∙ ((ƛ ((var 1 ∙ var 0) [ var 1 / 1 ])) ∙ var 0)
    →⟨⟩
      ƛ ƛ Z ∙ var 1 ∙ ((ƛ var 1 ∙ var 0) ∙ var 0)
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