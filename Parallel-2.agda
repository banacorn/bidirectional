module Parallel-2 where

open import Parallel

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality hiding ([_])


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

module ShiftVar where
  open import Data.Nat.Properties      
  open ≡-Reasoning

  shift-var-n-0-i : ∀ n i → shift-var n 0 i ≡ i
  shift-var-n-0-i zero i = +-identityʳ i
  shift-var-n-0-i (suc n) zero = refl
  shift-var-n-0-i (suc n) (suc i) = cong suc (shift-var-n-0-i n i)

  shift-var-lemma : ∀ n i x → shift-var n i x + 0 ≡ shift-var n i (x + 0)
  shift-var-lemma n i x = 
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
  shift-shift-var zero    (suc n) i x       = shift-var-lemma (suc n) i x
  shift-shift-var (suc m) zero    i x       = shift-var-on-site (suc m) i x
  shift-shift-var (suc m) (suc n) i zero    = refl
  shift-shift-var (suc m) (suc n) i (suc x) = cong suc (shift-shift-var m n i x)

  shift-shift-var-l-m : ∀ l m n i x → shift-var (suc l) m (shift-var (suc (l + n)) i x) ≡ shift-var (l + m + suc n) i (shift-var (suc l) m x)
  shift-shift-var-l-m l m n i zero = {!   !}
  shift-shift-var-l-m l m n i (suc x) = {!   !}

shift-shift : ∀ m n i N → shift m 0 (shift n i N) β→* shift n i (shift m 0 N)
shift-shift m n i (var x) = cong-var (ShiftVar.shift-shift-var m n i x)
shift-shift m n i (ƛ N) = cong-ƛ (shift-shift (suc m) (suc n) i N)
shift-shift m n i (M ∙ N) = cong-∙ (shift-shift m n i M) (shift-shift m n i N)

shift-shift-l-m : ∀ l m n i N → shift (suc l) m (shift (suc l + n) i N) β→* shift (l + m + suc n) i (shift (suc l) m N)
shift-shift-l-m l m n i (var x) = cong-var (ShiftVar.shift-shift-var-l-m l m n i x)
shift-shift-l-m l m n i (ƛ N) = cong-ƛ (shift-shift-l-m (suc l) m n i N)
shift-shift-l-m l m n i (M ∙ N) = cong-∙ (shift-shift-l-m l m n i M) (shift-shift-l-m l m n i N)

cong-shift-app-2-3 : ∀ n i M N → shift (suc (suc (suc (suc n)))) i M [ ƛ shift (suc n) i N / 3 ] β→* shift (suc (suc (suc n))) i (M [ ƛ N / 3 ])
cong-shift-app-2-3 n i (var zero) N = ε
cong-shift-app-2-3 n i (var suc zero) N = ε
cong-shift-app-2-3 n i (var suc (suc zero)) N = ε
cong-shift-app-2-3 n i (var suc (suc (suc zero))) N = cong-ƛ (shift-shift-l-m zero 3 n i N)
cong-shift-app-2-3 n i (var suc (suc (suc (suc x)))) N = ε
cong-shift-app-2-3 n i (ƛ M)   N = {!   !}
cong-shift-app-2-3 n i (L ∙ M) N = cong-∙ (cong-shift-app-2-3 n i L N) (cong-shift-app-2-3 n i M N)

cong-shift-app-2-2 : ∀ n i M N → shift (suc (suc (suc n))) i M [ ƛ shift (suc n) i N / 2 ] β→* shift (suc (suc n)) i (M [ ƛ N / 2 ])
cong-shift-app-2-2 n i (var zero) N = ε
cong-shift-app-2-2 n i (var suc zero) N = ε
cong-shift-app-2-2 n i (var suc (suc zero)) N = cong-ƛ (shift-shift-l-m zero 2 n i N)
cong-shift-app-2-2 n i (var suc (suc (suc x))) N = ε
cong-shift-app-2-2 n i (ƛ M)   N = cong-ƛ (cong-shift-app-2-3 n i M N)
cong-shift-app-2-2 n i (L ∙ M) N = cong-∙ (cong-shift-app-2-2 n i L N) (cong-shift-app-2-2 n i M N)

cong-shift-app-2 : ∀ n i M N → shift (suc (suc n)) i M [ ƛ shift (suc n) i N / 1 ] β→* shift (suc n) i (M [ ƛ N / 1 ])
cong-shift-app-2 n i (var zero)  N = ε
cong-shift-app-2 n i (var suc zero) N = cong-ƛ (shift-shift-l-m zero 1 n i N)
cong-shift-app-2 n i (var suc (suc x)) N = ε
cong-shift-app-2 n i (ƛ M)   N = cong-ƛ (cong-shift-app-2-2 n i M N)
cong-shift-app-2 n i (L ∙ M) N = cong-∙ (cong-shift-app-2 n i L N) (cong-shift-app-2 n i M N)


cong-shift-app-1 : ∀ n i M y → shift (suc (suc n)) i M [ var shift-var n i y / 1 ] β→* shift (suc n) i (M [ var y / 1 ])
cong-shift-app-1 n i (var zero)  y = ε
cong-shift-app-1 n i (var suc zero) y = cong-var (ShiftVar.shift-var-lemma-1 n i y)
cong-shift-app-1 n i (var suc (suc x)) y = ε
cong-shift-app-1 n i (ƛ M)   y = cong-ƛ {! !}
cong-shift-app-1 n i (M ∙ N) y = cong-∙ (cong-shift-app-1 n i M y) (cong-shift-app-1 n i N y)

cong-shift-app : (n i : ℕ) (M N : Term) → shift n i ((ƛ M) ∙ N) β→* shift n i (M [ N ])
cong-shift-app n i (var zero) (var x) = β-ƛ-∙ ◅ cong-var (ShiftVar.shift-var-lemma n i x)
cong-shift-app n i (var zero) (ƛ N)   = β-ƛ-∙ ◅ cong-ƛ (shift-shift 1 (suc n) i N)
cong-shift-app n i (var zero) (M ∙ N) = β-ƛ-∙ ◅ cong-∙ (shift-shift 0 n i M) (shift-shift 0 n i N)
cong-shift-app n i (var suc x) N      = β-ƛ-∙ ◅ ε
cong-shift-app n i (ƛ M)   (var y) = β-ƛ-∙ ◅ cong-ƛ (cong-shift-app-1 n i M y)
cong-shift-app n i (ƛ M)   (ƛ N)   = β-ƛ-∙ ◅ cong-ƛ (cong-shift-app-2 n i M N)
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

