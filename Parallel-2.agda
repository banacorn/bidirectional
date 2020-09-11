module Parallel-2 where

open import Parallel
import ShiftVar
import CMP
import Abs


open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties
open import Agda.Builtin.Bool

shift-shift : ∀ m n i N → shift m 0 (shift n i N) β→* shift n i (shift m 0 N)
shift-shift m n i (var x) = cong-var (ShiftVar.shift-shift-var m n i x)
shift-shift m n i (ƛ N) = cong-ƛ (shift-shift (suc m) (suc n) i N)
shift-shift m n i (M ∙ N) = cong-∙ (shift-shift m n i M) (shift-shift m n i N)

shift-shift-l-m' : ∀ l m n i N → shift l m (shift (l + n) i N) β→* shift (l + m + n) i (shift l m N)
shift-shift-l-m' l m n i (var x) = cong-var (ShiftVar.shift-shift-var-l-m' l m n i x)
shift-shift-l-m' l m n i (ƛ N) = cong-ƛ (shift-shift-l-m' (suc l) m n i N)
shift-shift-l-m' l m n i (M ∙ N) = cong-∙ (shift-shift-l-m' l m n i M) (shift-shift-l-m' l m n i N)

------------------------------------------------------------------------------
cong-shift-app : (n i : ℕ) (M N : Term) → shift n i ((ƛ M) ∙ N) β→* shift n i (M [ N ])
cong-shift-app n i (var zero) (var x) = β-ƛ-∙ ◅ cong-var (ShiftVar.shift-var-lemma' n i x)
cong-shift-app n i (var zero) (ƛ N)   = β-ƛ-∙ ◅ cong-ƛ (shift-shift 1 (suc n) i N)
cong-shift-app n i (var zero) (M ∙ N) = β-ƛ-∙ ◅ cong-∙ (shift-shift 0 n i M) (shift-shift 0 n i N)
cong-shift-app n i (var suc x) N      = β-ƛ-∙ ◅ ε
cong-shift-app n i (ƛ M)   N = β-ƛ-∙ ◅ cong-ƛ (Abs.lemma 0 n i M N)
cong-shift-app n i (K ∙ M) (var y) = β-ƛ-∙ ◅ cong-∙ {!   !} {!   !}
cong-shift-app n i (K ∙ M) (ƛ N)   = β-ƛ-∙ ◅ cong-∙ {!   !} {!   !}
cong-shift-app n i (K ∙ M) (L ∙ N) = β-ƛ-∙ ◅ cong-∙ {!   !} {!   !}

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

