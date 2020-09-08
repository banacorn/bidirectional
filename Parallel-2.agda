module Parallel-2 where

open import Parallel

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 

cong-shift-app-var-0 : {i : ℕ} (N : Term) → shift 0 (shift i N) β→* shift i (shift 0 N)
cong-shift-app-var-0 (var x) = {!   !}
cong-shift-app-var-0 (ƛ N)   = cong-ƛ (cong-shift-app-var-0 N)
cong-shift-app-var-0 (M ∙ N) = cong-∙ (cong-shift-app-var-0 M) (cong-shift-app-var-0 N)

cong-shift-app-var-1 : ∀ {i : ℕ} (N : Term) → var i β→* shift (suc i) (shift 0 N)
cong-shift-app-var-1 {i} (var x) = {!   !}
cong-shift-app-var-1 {i} (ƛ N)   = {!   !}
cong-shift-app-var-1 {i} (M ∙ N) = {!   !}
     

cong-shift-app-var : {i : ℕ} (x : ℕ) (N : Term) → shift i (var x) [ shift i N ] β→* shift i ((var x) [ N ])
cong-shift-app-var {zero} zero N = ε
cong-shift-app-var {suc i} zero N = {!   !}
    -- cong-shift-app-var-1 {i} N
cong-shift-app-var {i} (suc x) N = {!   !}

cong-shift-app-0 : ∀ i y → (var i) [ var (y + i) ] β→* var (y + zero + i)
cong-shift-app-0 zero y    = ε
cong-shift-app-0 (suc i) y = {!   !}

cong-shift-app : {i : ℕ} (M N : Term) → shift i ((ƛ M) ∙ N) β→* shift i (M [ N ])
cong-shift-app {i} (var zero) (var y) = β-ƛ-∙ ◅ cong-shift-app-0 i y
cong-shift-app {i} (var suc x) (var y) = {!   !}
cong-shift-app {i} (var x) (ƛ N)   = {!   !}
cong-shift-app {i} (var x) (L ∙ N) = {!   !}
cong-shift-app {i} (ƛ M)   (var y) = {!   !}
cong-shift-app {i} (ƛ M)   (ƛ N)   = {!   !}
cong-shift-app {i} (ƛ M)   (L ∙ N) = {!   !}
cong-shift-app {i} (K ∙ M) (var y) = {!   !}
cong-shift-app {i} (K ∙ M) (ƛ N)   = {!   !}
cong-shift-app {i} (K ∙ M) (L ∙ N) = {!   !}

cong-shift : {i : ℕ} {M N : Term} → M β→ N → shift i M β→* shift i N
cong-shift (β-ƛ M→N)        = cong-ƛ (cong-shift M→N)
cong-shift (β-ƛ-∙ {M} {N})  = cong-shift-app M N
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

