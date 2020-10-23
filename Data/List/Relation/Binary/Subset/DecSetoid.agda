------------------------------------------------------------------------
-- The extensional sublist relation over decidable setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Subset.DecSetoid
  {c ℓ} (S : DecSetoid c ℓ) where

-- import Data.List.Relation.Binary.Permutation.Setoid as SetoidPerm
-- import Data.List.Relation.Binary.Subset.Setoid as SetoidSubset
-- import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
--   as HeterogeneousProperties
open import Level using (_⊔_)

-- open DecSetoid S
-- open SetoidSubset setoid public
-- open DecSetoidEquality S

open Relation.Binary using (Rel)
open import Data.List using (List) 

------------------------------------------------------------------------
-- Subset relation

module _ where 
  open import Function using (_∘_)
  open import Data.List 
  open import Data.List.Membership.DecSetoid S using (_∈_; _∈?_)
  open import Relation.Nullary
  open import Data.List.Relation.Unary.Any public
  open import Data.List.Relation.Unary.Any.Properties using (¬Any[])

  open DecSetoid S

  infix 4 _⊆_ _⊈_
  _⊆_ : Rel (List Carrier) (c ⊔ ℓ)
  xs ⊆ ys = ∀ x → x ∈ xs → x ∈ ys

  _⊈_ : Rel (List Carrier) (c ⊔ ℓ)
  xs ⊈ ys = ¬ xs ⊆ ys

  -- lemma 
  ∈-cong : ∀ {xs x y} → x ≈ y → x ∈ xs → y ∈ xs
  ∈-cong x≈y (here P) = here (trans (sym x≈y) P)
  ∈-cong x≈y (there P) = there (∈-cong x≈y P)

  ∉[] : ∀ {x xs} → ¬ x ∷ xs ⊆ []
  ∉[] {x} {xs} P = ¬Any[] (∈-cong {[]} {x} {x} refl (P x (here refl)))

  ⊆-refl : ∀ {xs} → xs ⊆ xs
  ⊆-refl  x P = P
  
  ∷-mono : ∀ {xs ys x y} → x ≈ y → xs ⊆ ys → x ∷ xs ⊆ y ∷ ys
  ∷-mono x≈y P x (here Q) = here (trans Q x≈y)
  ∷-mono x≈y P x (there Q) = there (P x Q)

  ⊆-swap : ∀ {xs x y} → x ∷ y ∷ xs ⊆ y ∷ x ∷ xs
  ⊆-swap x (here P) = there (here P)
  ⊆-swap x (there (here P)) = here P
  ⊆-swap x (there (there P)) = there (there P)

  infix 4 _⊆?_
  _⊆?_ : Decidable _⊆_
  [] ⊆? ys = yes (λ x ())
  x ∷ xs ⊆? [] = no ∉[]
  x ∷ xs ⊆? y ∷ ys with x ∈? y ∷ ys 
  x ∷ xs ⊆? y ∷ ys | yes P with xs ⊆? y ∷ ys 
  ... | yes Q = yes λ where x (here R) → ∈-cong (sym R) P
                            x (there R) → Q x R
  ... | no ¬Q = no λ R → ¬Q λ x S → R x (there S)
  x ∷ xs ⊆? y ∷ ys | no ¬P = no λ Q → ¬P (Q x (here refl))

------------------------------------------------------------------------
-- Equivalence relation

module _ where 
  open DecSetoid S
  open import Data.Product
  open import Data.List 
  open import Relation.Binary.Construct.Intersection
  open import Function.Base using (flip)
  infix 4 _≋_
  _≋_ : Rel (List Carrier) (c ⊔ ℓ)
  _≋_ = _⊆_ ∩ flip _⊆_
  {-# DISPLAY _⊆_ ∩ flip _⊆_ = _≋_ #-}


  ∷-cong : ∀ {xs ys x y} → x ≈ y → xs ≋ ys → x ∷ xs ≋ y ∷ ys
  ∷-cong x≈y (xs⊆ys , ys⊆xs) = ∷-mono x≈y xs⊆ys , ∷-mono (sym x≈y) ys⊆xs

  ≋-swap : ∀ {xs x y} → x ∷ y ∷ xs ≋ y ∷ x ∷ xs
  ≋-swap = ⊆-swap , ⊆-swap

  open import Data.List.Relation.Binary.Permutation.Homogeneous
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  infix 4 _≋?_
  _≋?_ : Decidable _≋_
  _≋?_ = decidable _⊆?_ (flip _⊆?_)

------------------------------------------------------------------------
-- Relational properties

module _ where 
  open import Data.Product

  ≋-isEquivalence : IsEquivalence _≋_
  ≋-isEquivalence = record 
    { refl = (λ x z → z) , (λ x z → z) 
    ; sym = λ where (P , Q) → Q , P 
    ; trans = λ where (P , Q) (S , T) → (λ x U → S x (P x U)) , λ x V → Q x (T x V) 
    }

  -- shorthands
  ≋-refl : Reflexive _≋_ 
  ≋-refl = IsEquivalence.refl ≋-isEquivalence

  ≋-sym : Symmetric _≋_ 
  ≋-sym = IsEquivalence.sym ≋-isEquivalence

  ≋-trans : Transitive _≋_ 
  ≋-trans = IsEquivalence.trans ≋-isEquivalence

  ⊆-IsPreorder : IsPreorder _≋_ _⊆_
  ⊆-IsPreorder = record 
    { isEquivalence = ≋-isEquivalence
    ; reflexive = λ where (P , Q) x R → P x R
    ; trans = λ P Q x R → Q x (P x R)
    }

  ⊆-Antisymmetric : Antisymmetric _≋_ _⊆_
  ⊆-Antisymmetric P Q = P , Q

  ⊆-isPartialOrder : IsPartialOrder _≋_ _⊆_
  ⊆-isPartialOrder = record 
    { isPreorder = ⊆-IsPreorder
    ; antisym = ⊆-Antisymmetric }

  ⊆-isDecPartialOrder : IsDecPartialOrder _≋_ _⊆_
  ⊆-isDecPartialOrder = record
    { isPartialOrder = ⊆-isPartialOrder
    ; _≟_            = _≋?_
    ; _≤?_           = _⊆?_
    }

------------------------------------------------------------------------
-- Bundles

poset : Poset _ _ _
poset = record 
  { Carrier = List (DecSetoid.Carrier S)
  ; _≈_ = _≋_ 
  ; _≤_ = _⊆_ 
  ; isPartialOrder = ⊆-isPartialOrder 
  }

setoid : Setoid _ _
setoid = record 
  { Carrier = List (DecSetoid.Carrier S) 
  ; _≈_ = _≋_ 
  ; isEquivalence = ≋-isEquivalence 
  }

------------------------------------------------------------------------
-- Reasoning

module PosetReasoning where 
  open import Relation.Binary.Reasoning.PartialOrder poset public
module EqReasoning where 
  open import Relation.Binary.Reasoning.Setoid setoid public