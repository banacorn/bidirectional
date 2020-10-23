open import Relation.Binary using (Decidable; Setoid; DecSetoid)
open import Level 


module CP.Session3 {a} {b} (ChanDecSetoid : DecSetoid zero a) (TypeDecSetoid : DecSetoid zero b) where 

module TS = DecSetoid TypeDecSetoid


Type : Set
Type = DecSetoid.Carrier TypeDecSetoid

open DecSetoid ChanDecSetoid

Chan : Set
Chan = Carrier

module _ where 
  -- type of 
  infix 6 _∶_
  data TypeOf : Set a where 
    _∶_ : (x : Chan) → (A : Type) → TypeOf

  chanOf : TypeOf → Chan 
  chanOf (x ∶ _) = x

  import Relation.Binary.Construct.On as On
  
  decSetoid : DecSetoid _ _
  decSetoid = On.decSetoid ChanDecSetoid chanOf

open import Data.List.Relation.Binary.Subset.DecSetoid decSetoid
open import Data.List

Session : Set a
Session = List TypeOf


open import Relation.Nullary
open import Relation.Nullary.Decidable


open import Data.Product
open import Data.Maybe

seperate : (Γ : Session) → (x : Chan) → Maybe (∃[ Δ ] ∃[ A ] (Γ ≋ x ∶ A ∷ Δ))
seperate []          x = nothing
seperate (y ∶ A ∷ Γ) x with y ≟ x 
... | yes P = just (Γ , A , ∷-cong P ≋-refl)
... | no ¬P with seperate Γ x 
... | just (Δ , B , eq) = just (y ∶ A ∷ Δ , B , reasoning)
  where 
    open EqReasoning
    reasoning : y ∶ A ∷ Γ ≋ x ∶ B ∷ y ∶ A ∷ Δ
    reasoning = 
      begin
        y ∶ A ∷ Γ
      ≈⟨ ∷-cong refl eq ⟩
        y ∶ A ∷ x ∶ B ∷ Δ
      ≈⟨ ≋-swap ⟩
        x ∶ B ∷ y ∶ A ∷ Δ
      ∎
... | nothing = nothing

-- insertion 
infixl 5 _#_
_#_ : Session → TypeOf → Session
Γ # (x ∶ A) with seperate Γ x 
... | nothing = x ∶ A ∷ Γ
... | just (Δ , _ , _) = x ∶ A ∷ Δ

insert-idempotent : ∀ Γ x A → Γ # x ∶ A # x ∶ A ≋ Γ # x ∶ A
insert-idempotent Γ x A with seperate Γ x 
insert-idempotent Γ x A | nothing with seperate (x ∶ A ∷ Γ) x
... | nothing = {!   !}
... | just x₁ = {!   !}
insert-idempotent Γ x A | just x₁ = {!   !}
