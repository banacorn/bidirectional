module Parallel-2 where

open import Parallel

open import Data.Nat
open import Relation.Nullary 
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties
open import Agda.Builtin.Bool

x+i+j≡x+j+i : ∀ x j {i} → x + i + j ≡ x + j + i
x+i+j≡x+j+i x j {i} = 
    x + i + j
  ≡⟨ +-assoc x i j ⟩ 
    x + (i + j)
  ≡⟨ cong (λ z → x + z) (+-comm i j) ⟩ 
    x + (j + i)
  ≡⟨ sym (+-assoc x j i) ⟩ 
    x + j + i 
  ∎
  where 
    open ≡-Reasoning
    open import Data.Nat.Properties

module CMP where
  open import Data.Nat.Properties      
  open ≤-Reasoning

  1+x+k+n>x : ∀ {x k n} → suc (x + k + n) > x
  1+x+k+n>x {zero} = s≤s z≤n
  1+x+k+n>x {suc x} = s≤s 1+x+k+n>x

  2+x+k+n>x : ∀ {x k n} → suc (suc (x + k + n)) > x
  2+x+k+n>x {zero}  {k} {n} = s≤s z≤n
  2+x+k+n>x {suc x} {k} {n} = s≤s 2+x+k+n>x

  m+n≰x+m : ∀ {m n x} → n ≰ x → m + n > x + m
  m+n≰x+m {m} {n} {x} n≰x = begin 
      suc x + m 
    ≡⟨ +-comm (suc x) m ⟩ 
      m + suc x
    ≤⟨ +-monoʳ-≤ m (≰⇒> n≰x) ⟩ 
      m + n 
    ∎

  m+n≤x+m : ∀ {m n x} → n ≤ x → m + n ≤ x + m
  m+n≤x+m {m} {n} {x} n≤x = begin 
      m + n 
    ≤⟨ +-monoʳ-≤ m n≤x ⟩ 
      m + x 
    ≡⟨ +-comm m x ⟩ 
      x + m 
    ∎

  m+0≤x+m : ∀ m x → m + 0 ≤ x + m
  m+0≤x+m m x = begin 
      m + zero 
    ≡⟨ +-identityʳ m ⟩ 
      m 
    ≤⟨ m≤m+n m x ⟩ 
      m + x 
    ≡⟨ +-comm m x ⟩ 
      x + m 
    ∎

module ShiftVar where
  open import Data.Nat.Properties      
  open ≡-Reasoning

  shift-var-n-0-i : ∀ n i → shift-var n 0 i ≡ i
  shift-var-n-0-i zero i = +-identityʳ i
  shift-var-n-0-i (suc n) zero = refl
  shift-var-n-0-i (suc n) (suc i) = cong suc (shift-var-n-0-i n i)

  shift-var-lemma' : ∀ n i x → shift-var n i x + 0 ≡ shift-var n i (x + 0)
  shift-var-lemma' n i x = 
      shift-var n i x + zero
    ≡⟨ +-identityʳ (shift-var n i x) ⟩ 
      shift-var n i x
    ≡⟨ cong (shift-var n i) (sym (+-identityʳ x)) ⟩ 
      shift-var n i (x + zero)
    ∎

  shift-var-on-site : ∀ n i x → shift-var n 0 (x + i) ≡ shift-var n 0 x + i
  shift-var-on-site zero i x = x+i+j≡x+j+i x zero
  shift-var-on-site (suc n) i zero = shift-var-n-0-i (suc n) i
  shift-var-on-site (suc n) i (suc x) = cong suc (shift-var-on-site n i x)

  shift-var-lemma-1 : ∀ n i x → shift-var n i x + 1 ≡ shift-var (1 + n) i (x + 1)
  shift-var-lemma-1 zero i zero = +-comm i 1
  shift-var-lemma-1 zero i (suc x) = cong suc (x+i+j≡x+j+i x 1)
  shift-var-lemma-1 (suc n) i zero = refl
  shift-var-lemma-1 (suc n) i (suc x) = cong suc (shift-var-lemma-1 n i x)

  shift-shift-var : ∀ m n i x → shift-var m 0 (shift-var n i x) ≡ shift-var n i (shift-var m 0 x)
  shift-shift-var zero    zero    i x       = x+i+j≡x+j+i x 0
  shift-shift-var zero    (suc n) i x       = shift-var-lemma' (suc n) i x
  shift-shift-var (suc m) zero    i x       = shift-var-on-site (suc m) i x
  shift-shift-var (suc m) (suc n) i zero    = refl
  shift-shift-var (suc m) (suc n) i (suc x) = cong suc (shift-shift-var m n i x)

  shift-var-lemma-≡ : ∀ n i x → n ≡ x → i + x ≡ shift-var n i x 
  shift-var-lemma-≡ zero    i .0 refl = +-identityʳ i
  shift-var-lemma-≡ (suc n) i .(suc n) refl = 
      i + suc n
    ≡⟨ +-suc i n ⟩ 
      suc (i + n) 
    ≡⟨ cong suc (shift-var-lemma-≡ n i n refl) ⟩ 
      suc (shift-var n i n) 
    ∎
  
  shift-var-lemma-≤ : ∀ {n x} i → n ≤ x → i + x ≡ shift-var n i x 
  shift-var-lemma-≤ {zero}  {x}     i cmp       = +-comm i x
  shift-var-lemma-≤ {suc n} {suc x} i (s≤s cmp) =
      i + suc x
    ≡⟨ +-suc i x ⟩ 
      suc (i + x) 
    ≡⟨ cong suc (shift-var-lemma-≤ i cmp) ⟩ 
      suc (shift-var n i x) 
    ∎

  shift-var-lemma-> : ∀ {n i x} → n > x → x ≡ shift-var n i x 
  shift-var-lemma-> {suc n} {i} {zero}  n>x       = refl
  shift-var-lemma-> {suc n} {i} {suc x} (s≤s n>x) = cong suc (shift-var-lemma-> n>x)

  

  shift-shift-var-l-m'-0' : ∀ n i x m → shift-var n i x + m ≡ shift-var (m + n) i (x + m)
  shift-shift-var-l-m'-0' n i x m with n ≤? x
  ... | true because ofʸ p = 
          shift-var n i x + m 
        ≡⟨ cong (λ w → w + m) (sym (shift-var-lemma-≤ i p)) ⟩ 
          i + x + m 
        ≡⟨ +-assoc i x m ⟩ 
          i + (x + m)
        ≡⟨ shift-var-lemma-≤ {m + n} {x + m} i (CMP.m+n≤x+m p) ⟩ 
          shift-var (m + n) i (x + m) 
        ∎
  ... | false because ofⁿ ¬p = 
          shift-var n i x + m 
        ≡⟨ cong (λ w → w + m) (sym (shift-var-lemma-> (≰⇒> ¬p))) ⟩ 
          x + m 
        ≡⟨ shift-var-lemma-> (CMP.m+n≰x+m ¬p) ⟩ 
          shift-var (m + n) i (x + m) 
        ∎

  shift-shift-var-l-m' : ∀ l m n i x → shift-var l m (shift-var (l + n) i x) ≡ shift-var (l + m + n) i (shift-var l m x)
  shift-shift-var-l-m' zero    m n i x       = shift-shift-var-l-m'-0' n i x m
  shift-shift-var-l-m' (suc l) m n i zero    = refl
  shift-shift-var-l-m' (suc l) m n i (suc x) = cong suc (shift-shift-var-l-m' l m n i x)

shift-shift : ∀ m n i N → shift m 0 (shift n i N) β→* shift n i (shift m 0 N)
shift-shift m n i (var x) = cong-var (ShiftVar.shift-shift-var m n i x)
shift-shift m n i (ƛ N) = cong-ƛ (shift-shift (suc m) (suc n) i N)
shift-shift m n i (M ∙ N) = cong-∙ (shift-shift m n i M) (shift-shift m n i N)

shift-shift-l-m' : ∀ l m n i N → shift l m (shift (l + n) i N) β→* shift (l + m + n) i (shift l m N)
shift-shift-l-m' l m n i (var x) = cong-var (ShiftVar.shift-shift-var-l-m' l m n i x)
shift-shift-l-m' l m n i (ƛ N) = cong-ƛ (shift-shift-l-m' (suc l) m n i N)
shift-shift-l-m' l m n i (M ∙ N) = cong-∙ (shift-shift-l-m' l m n i M) (shift-shift-l-m' l m n i N)

-- shift-shift-l-m' : ∀ l m n i N → shift l m (shift (l + n) i N) β→* shift (l + m + n) i (shift l m N)

-- shift (suc (suc (m + n))) i (var x) [ ƛ shift (suc n) i N / suc m ] β→* shift (suc m + n) i ((var x) [ ƛ N / suc m ])
-- cong-shift-app-2-m-0 : ∀ m n i x N → shift (suc (suc (m + n))) i (var x) [ ƛ shift (suc n) i N / suc m ] β→* shift (suc m + n) i ((var x) [ ƛ N / suc m ])
-- cong-shift-app-2-m-0 m n i x N with compare x (suc m)
-- cong-shift-app-2-m-0 m n i x N | less .x k rewrite sym (ShiftVar.shift-var-lemma-> {suc (suc (x + k + n))} {i} {x} CMP.2+x+k+n>x) = {!   !}
-- cong-shift-app-2-m-0 m n i x N | equal .(suc m) = {!   !}
-- cong-shift-app-2-m-0 m n i x N | greater .(suc m) k = {!   !}


cong-shift-app-2-m-0-prop-1 : ∀ n i x k → shift-var (suc (suc (x + k + n))) i x ≡ x
cong-shift-app-2-m-0-prop-1 n i x k = sym (ShiftVar.shift-var-lemma-> {suc (suc (x + k + n))} {i} {x} CMP.2+x+k+n>x)

cong-shift-app-2-m-0-prop-2 : ∀ x k → compare x (suc (x + k)) ≡ less x k
cong-shift-app-2-m-0-prop-2 zero k = refl
cong-shift-app-2-m-0-prop-2 (suc x) k rewrite cong-shift-app-2-m-0-prop-2 x k = refl

cong-shift-app-2-m-0-prop-3 : ∀ m n i → shift-var (suc (m + n)) i m ≡ m
cong-shift-app-2-m-0-prop-3 m n i = sym (ShiftVar.shift-var-lemma-> {suc (m + n)} {i} {m} (s≤s (m≤m+n m n)))

cong-shift-app-2-m-0-prop-4 : ∀ m → compare m m ≡ equal m 
cong-shift-app-2-m-0-prop-4 zero = refl
cong-shift-app-2-m-0-prop-4 (suc m) rewrite cong-shift-app-2-m-0-prop-4 m = refl


cong-shift-app-2-m-0-prop-5 : ∀ m n k i → m + n ≤ m + k → shift-var (m + n) i (m + k) ≡ m + (k + i)
cong-shift-app-2-m-0-prop-5 m n k i m+n≤m+k = 
    shift-var (m + n) i (m + k) 
  ≡⟨ sym (ShiftVar.shift-var-lemma-≤ i m+n≤m+k) ⟩ 
    i + (m + k) 
  ≡⟨ +-comm i (m + k) ⟩ 
    m + k + i 
  ≡⟨ +-assoc m k i ⟩ 
    m + (k + i) ∎
  where 
    open ≡-Reasoning

cong-shift-app-2-m-0-prop-6 : ∀ m i k → compare (suc (m + (k + i))) m ≡ greater m (k + i)
cong-shift-app-2-m-0-prop-6 zero    i k = refl
cong-shift-app-2-m-0-prop-6 (suc m) i k rewrite cong-shift-app-2-m-0-prop-6 m i k = refl

cong-shift-app-2-m-0-prop-7 : ∀ m n k i → m + n ≰ m + k → shift-var (m + n) i (m + k) ≡ m + k
cong-shift-app-2-m-0-prop-7 m n k i rel = sym (ShiftVar.shift-var-lemma-> {m + n} {i} {m + k} (≰⇒> rel))

cong-shift-app-2-m-0-prop-8 : ∀ m k → compare (suc (m + k)) m ≡ greater m k
cong-shift-app-2-m-0-prop-8 zero    k = refl 
cong-shift-app-2-m-0-prop-8 (suc m) k rewrite cong-shift-app-2-m-0-prop-8 m k = refl 

cong-shift-app-2-m-0 : ∀ m n i x N → subst-var (ƛ shift (suc n) i N) (compare (shift-var (suc (suc (m + n))) i x) (suc m)) β→* shift (suc (m + n)) i (subst-var (ƛ N) (compare x (suc m)))
cong-shift-app-2-m-0 m n i x N with compare x (suc m)
... | less    .x       k rewrite cong-shift-app-2-m-0-prop-1 n i x k 
                               | cong-shift-app-2-m-0-prop-2 x k 
                               = cong-var (ShiftVar.shift-var-lemma-> {suc (x + k + n)} {i} {x} CMP.1+x+k+n>x)
... | equal   .(suc m)   rewrite cong-shift-app-2-m-0-prop-3 m n i 
                               | cong-shift-app-2-m-0-prop-4 m 
                               = cong-ƛ (shift-shift-l-m' 1 (suc m) n i N)
... | greater .(suc m) k with m + n ≤? m + k
... | true because ofʸ p rewrite cong-shift-app-2-m-0-prop-5 m n k i p
                               | cong-shift-app-2-m-0-prop-6 m i k = ε
... | false because ofⁿ ¬p rewrite cong-shift-app-2-m-0-prop-7 m n k i ¬p 
                               | cong-shift-app-2-m-0-prop-8 m k = ε

--  compare (shift-var (suc (suc (x + k + n))) i x) (suc (x + k)))
cong-shift-app-2-m : ∀ m n i M N → shift (suc (suc (m + n))) i M [ ƛ shift (suc n) i N / suc m ] β→* shift (suc m + n) i (M [ ƛ N / suc m ])
cong-shift-app-2-m m n i (var x) N = cong-shift-app-2-m-0 m n i x N
cong-shift-app-2-m m n i (ƛ M)   N = cong-ƛ (cong-shift-app-2-m (suc m) n i M N)
cong-shift-app-2-m m n i (L ∙ M) N = cong-∙ (cong-shift-app-2-m m n i L N) (cong-shift-app-2-m m n i M N) 

cong-shift-app-1 : ∀ n i M y → shift (suc (suc n)) i M [ var shift-var n i y / 1 ] β→* shift (suc n) i (M [ var y / 1 ])
cong-shift-app-1 n i (var zero)  y = ε
cong-shift-app-1 n i (var suc zero) y = cong-var (ShiftVar.shift-var-lemma-1 n i y)
cong-shift-app-1 n i (var suc (suc x)) y = ε
cong-shift-app-1 n i (ƛ M)   y = cong-ƛ {!  !}
cong-shift-app-1 n i (M ∙ N) y = cong-∙ (cong-shift-app-1 n i M y) (cong-shift-app-1 n i N y)

cong-shift-app : (n i : ℕ) (M N : Term) → shift n i ((ƛ M) ∙ N) β→* shift n i (M [ N ])
cong-shift-app n i (var zero) (var x) = β-ƛ-∙ ◅ cong-var (ShiftVar.shift-var-lemma' n i x)
cong-shift-app n i (var zero) (ƛ N)   = β-ƛ-∙ ◅ cong-ƛ (shift-shift 1 (suc n) i N)
cong-shift-app n i (var zero) (M ∙ N) = β-ƛ-∙ ◅ cong-∙ (shift-shift 0 n i M) (shift-shift 0 n i N)
cong-shift-app n i (var suc x) N      = β-ƛ-∙ ◅ ε
cong-shift-app n i (ƛ M)   (var y) = β-ƛ-∙ ◅ cong-ƛ (cong-shift-app-1 n i M y)
cong-shift-app n i (ƛ M)   (ƛ N)   = β-ƛ-∙ ◅ cong-ƛ (cong-shift-app-2-m 0 n i M N)
cong-shift-app n i (ƛ M)   (L ∙ N) = {!   !}
cong-shift-app n i (K ∙ M) (var y) = {!   !}
cong-shift-app n i (K ∙ M) (ƛ N)   = {!   !}
cong-shift-app n i (K ∙ M) (L ∙ N) = {!   !}

cong-shift : {n i : ℕ} {M N : Term} → M β→ N → shift n i M β→* shift n i N
cong-shift (β-ƛ M→N)        = cong-ƛ (cong-shift M→N)
cong-shift (β-ƛ-∙ {M} {N})  = cong-shift-app _ _ M N
cong-shift (β-∙-l M→N)      = cong-∙-l (cong-shift M→N)
cong-shift (β-∙-r M→N)      = cong-∙-r (cong-shift M→N)


cong-[]-r : ∀ L {M N i} → M β→ N → L [ M / i ] β→* L [ N / i ]
cong-[]-r (var x) {M} {N} {i} M→N with compare x i 
cong-[]-r (var x) {M} {N} {.(suc (x + k))}  M→N | less .x k = ε
cong-[]-r (var x) {M} {N} {.x}              M→N | equal .x = cong-shift M→N
cong-[]-r (var .(suc (m + k))) {M} {N} {.m} M→N | greater m k = ε
cong-[]-r (ƛ L)   M→N = cong-ƛ (cong-[]-r L M→N)
cong-[]-r (K ∙ L) M→N = cong-∙-l (cong-[]-r K M→N) ◅◅ cong-∙-r (cong-[]-r L M→N)


cong-[]-l : ∀ {M N L i} → M β→ N → M [ L / i ] β→* N [ L / i ]
cong-[]-l {ƛ M}                 (β-ƛ M→N)   = cong-ƛ   (cong-[]-l M→N)
cong-[]-l {.(ƛ K) ∙ M} {L = L}  (β-ƛ-∙ {K}) = {!   !}
cong-[]-l {K ∙ M}               (β-∙-l M→N) = cong-∙-l (cong-[]-l M→N)
cong-[]-l {K ∙ M}               (β-∙-r M→N) = cong-∙-r (cong-[]-l M→N)



cong-[] : {M M' N N' : Term} → M β→* M' → N β→* N' → M [ N ] β→* M' [ N' ]
cong-[] {M} ε            ε            = ε
cong-[] {M} {N = L} {N'} ε (_◅_ {j = N} L→N N→N') = M[L]→M[N] ◅◅ M[N]→M[N']
    where 
        M[L]→M[N] : M [ L ] β→* M [ N ]
        M[L]→M[N] = cong-[]-r M L→N

        M[N]→M[N'] : M [ N ] β→* M [ N' ]
        M[N]→M[N'] = cong-[] {M} ε N→N'
cong-[] {M} (K→M ◅ M→M') N→N' = cong-[]-l K→M ◅◅ cong-[] M→M' N→N'

from-parallel : ∀ {M N} → M β⇒ N → M β→* N
from-parallel β-var             = ε
from-parallel (β-ƛ M⇒N)         = cong-ƛ (from-parallel M⇒N)
from-parallel (β-∙ M⇒M' N⇒N')   = cong-∙ (from-parallel M⇒M') (from-parallel N⇒N')
from-parallel (β-ƛ-∙ M⇒M' N⇒N') = return β-ƛ-∙ ◅◅ cong-[] (from-parallel M⇒M') (from-parallel N⇒N') 

