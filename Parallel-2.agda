module Parallel-2 where

open import Parallel

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality hiding ([_])

-- cong-shift-app-var-0 : {i : ℕ} (N : Term) → shift 0 (shift i N) β→* shift i (shift 0 N)
-- cong-shift-app-var-0 (var x) = {!   !}
-- cong-shift-app-var-0 (ƛ N)   = cong-ƛ (cong-shift-app-var-0 N)
-- cong-shift-app-var-0 (M ∙ N) = cong-∙ (cong-shift-app-var-0 M) (cong-shift-app-var-0 N)

-- cong-shift-app-var-1 : ∀ {i : ℕ} (N : Term) → var i β→* shift (suc i) (shift 0 N)
-- cong-shift-app-var-1 {i} (var x) = {!   !}
-- cong-shift-app-var-1 {i} (ƛ N)   = {!   !}
-- cong-shift-app-var-1 {i} (M ∙ N) = {!   !}
     

-- cong-shift-app-var : {i : ℕ} (x : ℕ) (N : Term) → shift i (var x) [ shift i N ] β→* shift i ((var x) [ N ])
-- cong-shift-app-var {zero} zero N = ε
-- cong-shift-app-var {suc i} zero N = {!   !}
--     -- cong-shift-app-var-1 {i} N
-- cong-shift-app-var {i} (suc x) N = {!   !}


-- var     (shift-var n i y + 0) β→* var      shift-var n i (y + 0)
-- var suc (shift-var n i y + 0) β→* var suc (shift-var n i (y + 0))

cong-shift-app-0 : ∀ n i x y → shift n i ((ƛ var x) ∙ var y) β→* shift n i ((var x) [ var y ])
cong-shift-app-0 n       i zero          y       = {!   !}
cong-shift-app-0 zero    i (suc x)       y       = β-ƛ-∙ ◅ ε
cong-shift-app-0 (suc n) i (suc zero)    y       = β-ƛ-∙ ◅ ε
cong-shift-app-0 (suc n) i (suc (suc x)) zero    = β-ƛ-∙ ◅ ε
cong-shift-app-0 (suc n) i (suc (suc x)) (suc y) = β-ƛ-∙ ◅ ε

cong-var-suc : ∀ {x y} → var x β→* var y → var suc x β→* var suc y
cong-var-suc {x} {.x} ε = ε


cong-var-≡ : ∀ {x y} → x ≡ y → var x β→* var y
cong-var-≡ {x} {y} refl = ε

cong-shift-app-0' : ∀ n i y → (var zero) [ var shift-var n i y ] β→* var shift-var n i (y + zero)
cong-shift-app-0' zero i y = cong-var-≡ (
    y + i + zero 
  ≡⟨ +-identityʳ (y + i) ⟩ 
    y + i 
  ≡⟨ cong (λ x → x + i) (sym (+-identityʳ y)) ⟩ 
    y + zero + i ∎)
  where 
    open ≡-Reasoning
    open import Data.Nat.Properties
cong-shift-app-0' (suc n) i zero = ε
cong-shift-app-0' (suc n) i (suc y) = cong-var-suc (cong-shift-app-0' n i y)

cong-shift-app : (n i : ℕ) (M N : Term) → shift n i ((ƛ M) ∙ N) β→* shift n i (M [ N ])
cong-shift-app n i (var zero) (var y) = β-ƛ-∙ ◅ cong-shift-app-0' n i y
cong-shift-app n i (var suc x) (var y) = β-ƛ-∙ ◅ ε
cong-shift-app n i (var x) (ƛ N)   = {!   !}
cong-shift-app n i (var x) (L ∙ N) = {!   !}
cong-shift-app n i (ƛ M)   (var y) = {!   !}
cong-shift-app n i (ƛ M)   (ƛ N)   = {!   !}
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

