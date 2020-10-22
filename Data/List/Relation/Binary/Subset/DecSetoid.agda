------------------------------------------------------------------------
-- The extensional sublist relation over decidable setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Subset.DecSetoid
  {c ℓ} (S : DecSetoid c ℓ) where

-- import Data.List.Relation.Binary.Permutation.Setoid as SetoidPerm
import Data.List.Relation.Binary.Subset.Setoid as SetoidSubset
-- import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
--   as HeterogeneousProperties
open import Level using (_⊔_)

open DecSetoid S
open SetoidSubset setoid public
-- open DecSetoidEquality S

open Relation.Binary using (Rel)
open import Data.List using (List) 

------------------------------------------------------------------------
-- Subset relation

module _ where 
  open import Data.List 
  open import Data.List.Membership.DecSetoid S using (_∈_; _∈?_)
  open import Relation.Nullary
  open import Data.List.Relation.Unary.Any
  open import Data.List.Relation.Unary.Any.Properties using (¬Any[])

  -- lemma 
  ∈-cong : ∀ {xs x y} → x ≈ y → x ∈ xs → y ∈ xs
  ∈-cong x≈y (here P) = here (trans (sym x≈y) P)
  ∈-cong x≈y (there P) = there (∈-cong x≈y P)

  infix 4 _⊆?_
  _⊆?_ : Decidable _⊆_
  [] ⊆? ys = yes (λ ())
  x ∷ xs ⊆? [] = no (λ P → ¬Any[] (∈-cong refl (P (here refl))))
  x ∷ xs ⊆? y ∷ ys with x ∈? y ∷ ys 
  x ∷ xs ⊆? y ∷ ys | yes P with xs ⊆? y ∷ ys 
  ... | yes Q = yes (λ where (here R) → ∈-cong (sym R) P
                             (there R) → Q R)
  ... | no ¬Q = no (λ R → ¬Q (λ where y∈xs → R (there y∈xs)))
  x ∷ xs ⊆? y ∷ ys | no ¬P = no (λ Q → ¬P (Q (here refl)))


------------------------------------------------------------------------
-- Equivalence relation

module _ where 

  open import Relation.Binary.Construct.Intersection
  _≋_ : Rel (List Carrier) (c ⊔ ℓ)
  _≋_ = _⊆_ ∩ _⊆_

  open import Data.List.Relation.Binary.Permutation.Homogeneous
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  infix 4 _≋?_
  _≋?_ : Decidable _≋_
  _≋?_ = decidable _⊆?_ _⊆?_

-- ------------------------------------------------------------------------
-- -- Relational properties

-- open import Data.List 
-- open import Data.List.Membership.DecSetoid S
-- open import Relation.Nullary
-- open import Relation.Nullary.Decidable

-- open import Data.List.Relation.Unary.Any

-- open import Data.List.Relation.Unary.Any.Properties

-- -- lemma 
-- ∈-cong : ∀ {xs x y} → x ≈ y → x ∈ xs → y ∈ xs
-- ∈-cong x≈y (here P) = here (trans (sym x≈y) P)
-- ∈-cong x≈y (there P) = there (∈-cong x≈y P)

-- infix 4 _⊆?_
-- _⊆?_ : Decidable _⊆_
-- [] ⊆? ys = yes (λ ())
-- x ∷ xs ⊆? [] = no (λ P → ¬Any[] (∈-cong refl (P (here refl))))
-- x ∷ xs ⊆? y ∷ ys with x ∈? y ∷ ys 
-- x ∷ xs ⊆? y ∷ ys | yes P with xs ⊆? y ∷ ys 
-- ... | yes Q = yes (λ where (here R) → ∈-cong (sym R) P
--                            (there R) → Q R)
-- ... | no ¬Q = no (λ R → ¬Q (λ where y∈xs → R (there y∈xs)))
-- x ∷ xs ⊆? y ∷ ys | no ¬P = no (λ Q → ¬P (Q (here refl)))

-- open import Data.List.Relation.Binary.Subset.Setoid.Properties using (⊆-isPreorder)

-- -- ⊆-isPartialOrder : IsPartialOrder _≋_ _⊆_
-- -- ⊆-isPartialOrder = record 
-- --   { isPreorder = ⊆-isPreorder setoid
-- --   ; antisym = {!   !} }

-- open import Data.Empty using (⊥-elim)

-- ⊆-Antisymmetric : Antisymmetric _≋_ _⊆_
-- ⊆-Antisymmetric {[]} {[]} xs⊆ys ys⊆xs = []
-- ⊆-Antisymmetric {[]} {y ∷ ys} xs⊆ys ys⊆xs = ⊥-elim (¬Any[] (ys⊆xs (here refl)))
-- ⊆-Antisymmetric {x ∷ xs} {[]} xs⊆ys ys⊆xs = ⊥-elim (¬Any[] (xs⊆ys (here refl)))
-- ⊆-Antisymmetric {x ∷ xs} {y ∷ ys} xs⊆ys ys⊆xs = {!   !}


-- ⊆-isPartialOrder : IsPartialOrder _≋_ _⊆_
-- ⊆-isPartialOrder = record 
--   { isPreorder = ⊆-isPreorder setoid -- ⊆-isPreorder setoid
--   ; antisym = {!   !} }

-- -- ⊆-isDecPartialOrder : IsDecPartialOrder _≋_ _⊆_
-- -- ⊆-isDecPartialOrder = record
-- --   { isPartialOrder = ⊆-isPartialOrder
-- --   ; _≟_            = _≋?_
-- --   ; _≤?_           = _⊆?_
-- --   }