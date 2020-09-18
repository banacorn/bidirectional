module Parallel where

open import Base 
open import Subst
open import Reduction

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

