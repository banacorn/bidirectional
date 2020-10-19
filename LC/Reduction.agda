module LC.Reduction where 


open import LC.Base 
open import LC.Subst  

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary

-- β-reduction
infix 3 _β→_
data _β→_ : Term → Term → Set where 

  β-ƛ-∙ : ∀ {M N} → ((ƛ M) ∙ N) β→ (M [ N ])

  β-ƛ : ∀ {M N} → M β→ N → ƛ M β→ ƛ N

  β-∙-l : ∀ {L M N} → M β→ N → M ∙ L β→ N ∙ L

  β-∙-r : ∀ {L M N} → M β→ N → L ∙ M β→ L ∙ N

open import Relation.Binary.Construct.Closure.ReflexiveTransitive 

infix  2 _β→*_ 
_β→*_ : Term → Term → Set
_β→*_ = Star _β→_
{-# DISPLAY Star _β→_ = _β→*_ #-}

open import Relation.Binary.PropositionalEquality hiding ([_]; preorder)

≡⇒β→* : ∀ {M N} → M ≡ N → M β→* N
≡⇒β→* refl = ε

cong-var : ∀ {x y} → x ≡ y → var x β→* var y
cong-var {x} {y} refl = ε

cong-ƛ : {M N : Term} → M β→* N → ƛ M β→* ƛ N
cong-ƛ = gmap _ β-ƛ

cong-∙-l : {L M N : Term} → M β→* N → M ∙ L β→* N ∙ L
cong-∙-l = gmap _ β-∙-l

cong-∙-r : {L M N : Term} → M β→* N → L ∙ M β→* L ∙ N
cong-∙-r = gmap _ β-∙-r 

cong-∙ : {M M' N N' : Term} → M β→* M' → N β→* N' → M ∙ N β→* M' ∙ N'
cong-∙ M→M' N→N' = (cong-∙-l M→M') ◅◅ (cong-∙-r N→N')


open import LC.Subst.Term

cong-lift : {n i : ℕ} {M N : Term} → M β→ N → lift n i M β→* lift n i N
cong-lift (β-ƛ M→N)        = cong-ƛ (cong-lift M→N)
cong-lift (β-ƛ-∙ {M} {N})  = β-ƛ-∙ ◅ ≡⇒β→* (lemma M N)
cong-lift (β-∙-l M→N)      = cong-∙-l (cong-lift M→N)
cong-lift (β-∙-r M→N)      = cong-∙-r (cong-lift M→N)

cong-[]-r : ∀ L {M N i} → M β→ N → L [ M / i ] β→* L [ N / i ]
cong-[]-r (var x) {M} {N} {i} M→N with match x i 
... | Under _ = ε
... | Exact _ = cong-lift M→N
... | Above _ _ = ε
cong-[]-r (ƛ L)   M→N = cong-ƛ (cong-[]-r L M→N)
cong-[]-r (K ∙ L) M→N = cong-∙ (cong-[]-r K M→N) (cong-[]-r L M→N)


cong-[]-l : ∀ {M N L i} → M β→ N → M [ L / i ] β→* N [ L / i ]
cong-[]-l {ƛ M}                 (β-ƛ M→N)   = cong-ƛ   (cong-[]-l M→N)
cong-[]-l {.(ƛ K) ∙ M} {L = L}  (β-ƛ-∙ {K}) = β-ƛ-∙ ◅ ≡⇒β→* (subst-lemma K M L)
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
