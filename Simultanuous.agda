module Simultanuous where

open import Base 
open import Subst
open import Reduction

open import Data.Nat
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 

-- open import Relation.Binary.PropositionalEquality hiding ([_]; preorder)

-- infixl 4 _*
-- data _* : Term → Set where 
--     *-var : (M : Term) → M *
--     *-ƛ : ∀ {M} → ƛ M * → M *
--     *-∙ : ∀ {M N} → M ∙ N * → M * ∙ N *