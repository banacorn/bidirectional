module LC.Parallel where

open import LC.Base 
open import LC.Subst
open import LC.Reduction

open import Data.Nat
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 

-- parallel β-reduction
infix 3 _β⇒_
data _β⇒_ : Term → Term → Set where 

  β-var : {n : ℕ} → var n β⇒ var n

  β-ƛ : ∀ {M M'} → (M⇒M' : M β⇒ M') → ƛ M β⇒ ƛ M'

  β-∙ : ∀ {M M' N N'} → (M⇒M' : M β⇒ M') → (N⇒N' : N β⇒ N') → M ∙ N β⇒ M' ∙ N'

  β-ƛ-∙ : ∀ {M M' N N'} → (M⇒M' : M β⇒ M') → (N⇒N' : N β⇒ N') → (ƛ M) ∙ N β⇒ M' [ N' ]

-- properties
β⇒identity : ∀ {M} → M β⇒ M
β⇒identity {var x} = β-var
β⇒identity {ƛ M}   = β-ƛ β⇒identity
β⇒identity {M ∙ N} = β-∙ β⇒identity β⇒identity

to-parallel : ∀ {M N} → M β→ N → M β⇒ N 
to-parallel β-ƛ-∙       = β-ƛ-∙ β⇒identity β⇒identity
to-parallel (β-ƛ M→N)   = β-ƛ (to-parallel M→N)
to-parallel (β-∙-l M→N) = β-∙ (to-parallel M→N) β⇒identity
to-parallel (β-∙-r M→N) = β-∙ β⇒identity (to-parallel M→N)


from-parallel : ∀ {M N} → M β⇒ N → M β→* N
from-parallel β-var             = ε
from-parallel (β-ƛ M⇒N)         = cong-ƛ (from-parallel M⇒N)
from-parallel (β-∙ M⇒M' N⇒N')   = cong-∙ (from-parallel M⇒M') (from-parallel N⇒N')
from-parallel (β-ƛ-∙ M⇒M' N⇒N') = return β-ƛ-∙ ◅◅ cong-[] (from-parallel M⇒M') (from-parallel N⇒N') 

open import Relation.Binary.PropositionalEquality hiding ([_]; preorder)

≡⇒β⇒ : ∀ {M N} → M ≡ N → M β⇒ N
≡⇒β⇒ refl = β⇒identity

module Cong where 

  open import LC.Subst.Term
  open import LC.Subst.Var


  β⇒cong-lift-ƛ : ∀ {n i M M' N N'} → M β⇒ M' → N β⇒ N' → (ƛ lift (suc n) i M) ∙ lift n i N β⇒ lift n i (M' [ N' ])
  β⇒cong-lift-ƛ β-var N→N' = {!   !}
  β⇒cong-lift-ƛ (β-ƛ M→M') N→N' = {!  !}
  β⇒cong-lift-ƛ (β-∙ M→M' M→M'') N→N' = {!   !}
  β⇒cong-lift-ƛ (β-ƛ-∙ M→M' M→M'') N→N' = {!    !}

  β⇒cong-lift : ∀ {n i M N} → M β⇒ N → lift n i M β⇒ lift n i N
  β⇒cong-lift β-var = β-var
  β⇒cong-lift (β-ƛ M→N) = β-ƛ (β⇒cong-lift M→N)
  β⇒cong-lift (β-∙ M→M' N→N') = β-∙ (β⇒cong-lift M→M') (β⇒cong-lift N→N')
  β⇒cong-lift (β-ƛ-∙ M→M' N→N') = β⇒cong-lift-ƛ M→M' N→N'


  β⇒cong-subst-var-match : ∀ {n i M N} → M β⇒ N → subst-var (match n i) M β⇒ subst-var (match n i) N
  β⇒cong-subst-var-match {n} {i} M→N with match n i
  ... | Under n<i = β-var
  ... | Exact n≡i = β⇒cong-lift M→N
  ... | Above v v≥i = β-var

  open import Relation.Binary.PropositionalEquality hiding ([_]; preorder)

  module Temp where 

    lemma-1 : ∀ i m n o → (ƛ subst-var (match m (suc i)) (var n)) ∙ subst-var (match o i) (var n) ≡ (var m) [ var o ] [ var n / i ]
    lemma-1 i m n o with match m (suc i)
    ... | Under m<i+1 = {!   !}
    ... | Exact m≡i+1 = {!   !}
    ... | Above v v≥i+1 = {!   !}

    lemma-1-1 : ∀ i m n → subst-var (match m (suc i)) (var n) β⇒ {!   !}
    lemma-1-1 i m n = {!   !}

  β⇒cong-[]-ƛ-∙ : ∀ {i M M' N N' O O'} → M β⇒ M' → N β⇒ N' → O β⇒ O' → (ƛ M [ O / suc i ]) ∙ N [ O / i ] β⇒ (M' [ N' ]) [ O' / i ]
  β⇒cong-[]-ƛ-∙ {zero} (β-var {n}) (β-var {m}) (β-var {o}) = {!   !}
  β⇒cong-[]-ƛ-∙ {suc i} (β-var {n}) (β-var {m}) (β-var {o}) = {!   !}
  β⇒cong-[]-ƛ-∙ β-var β-var (β-ƛ O→O') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var β-var (β-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var β-var (β-ƛ-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ N→N') β-var = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ N→N') (β-ƛ O→O') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ N→N') (β-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ N→N') (β-ƛ-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-∙ N→N' N→N'') β-var = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-∙ N→N' N→N'') (β-ƛ O→O') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-∙ N→N' N→N'') (β-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-∙ N→N' N→N'') (β-ƛ-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ-∙ N→N' N→N'') β-var = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ-∙ N→N' N→N'') (β-ƛ O→O') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ-∙ N→N' N→N'') (β-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ β-var (β-ƛ-∙ N→N' N→N'') (β-ƛ-∙ O→O' O→O'') = {!   !}
  β⇒cong-[]-ƛ-∙ (β-ƛ M→M') N→N' O→O' = {!   !}
  β⇒cong-[]-ƛ-∙ (β-∙ M→M' M→M'') N→N' O→O' = {!   !}
  β⇒cong-[]-ƛ-∙ (β-ƛ-∙ M→M' M→M'') N→N' O→O' = {!   !}

  β⇒cong-[] : ∀ {i M M' N N'} → M β⇒ M' → N β⇒ N' → M [ N / i ] β⇒ M' [ N' / i ]
  β⇒cong-[] {i} (β-var {n}) N→N' = β⇒cong-subst-var-match {n} {i} N→N'
  β⇒cong-[] (β-ƛ M→M') N→N' = β-ƛ (β⇒cong-[] M→M' N→N')
  β⇒cong-[] (β-∙ M→M' M→M'') N→N' = β-∙ (β⇒cong-[] M→M' N→N') (β⇒cong-[] M→M'' N→N')
  β⇒cong-[] (β-ƛ-∙ M→M' M→M'') N→N' = {!   !}
    -- β⇒cong-[]-ƛ-∙ M→M' M→M'' N→N'
    -- β-∙ {!   !} {!   !}

    -- (ƛ M [ N₁ / suc i ]) ∙ N [ N₁ / i ] β⇒ M' [ N' ] [ N'' / i ]

    -- ((ƛ M) ∙ N) → M' [ N' ]
    -- ((ƛ M) ∙ N) [ N₁ / i ] β⇒ M' [ N' ] [ N'' / i ]
    --  M→M' N→N'  !} (β⇒cong-[] M→M'' N→N')

  -- β⇒cong-[] {i} {var x} {.(var x)} {var y} {.(var y)} β-var β-var with match x i 
  -- ... | Under x<i = β-var
  -- ... | Exact x≡i = β-var
  -- ... | Above v v≥i = β-var
  -- β⇒cong-[] {i} {var x} {.(var x)} {ƛ N} {.(ƛ _)} β-var (β-ƛ N→N') with match x i
  -- ... | Under x<i = β-var
  -- ... | Exact x≡i = β-ƛ (β⇒cong-lift N→N')
  -- ... | Above v v≥i = β-var
  -- β⇒cong-[] {i} {var x} {.(var x)} {N ∙ O} {N'} β-var N→N' with match x i
  -- ... | Under x<i = β-var
  -- ... | Exact x≡i = {!   !}
  -- ... | Above v v≥i = β-var
  -- β⇒cong-[] {i} {ƛ M} {M'} {N} {N'} M→M' N→N' = {!   !}
  -- β⇒cong-[] {i} {M ∙ K} {M'} {N} {N'} M→M' N→N' = {!   !}

β⇒cong-[] : ∀ {M M' N N'} → M β⇒ M' → N β⇒ N' → M [ N ] β⇒ M' [ N' ]
β⇒cong-[] = Cong.β⇒cong-[] 