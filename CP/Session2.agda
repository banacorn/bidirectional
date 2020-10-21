open import Relation.Binary using (Decidable; DecSetoid)
open import Level 


module CP.Session2 {a} (ChanSetoid : DecSetoid zero a) (Type : Set) where 

Chan : Set
Chan = DecSetoid.Carrier ChanSetoid

_≟Chan_ = DecSetoid._≟_ ChanSetoid
_≈Chan_ = DecSetoid._≈_ ChanSetoid
_≉Chan_ = DecSetoid._≉_ ChanSetoid

infixl 5 _,_∶_ 
data Session : Set a where 
    _,_∶_ : Session → Chan → Type → Session
    _++_ : Session → Session → Session
    ∅ : Session


-- open import Data.Bool hiding (_≟_)

-- open import Data.Empty 
-- open import Data.Unit  
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- open import Relation.Binary.PropositionalEquality


infix 4 _∋_
data _∋_ : (Γ : Session) → (x : Chan) → Set a where
  here  : ∀ {Γ x y A} → x ≈Chan y → Γ , y ∶ A ∋ x
  there : ∀ {Γ x y A} → x ≉Chan y → Γ         ∋ x → Γ , y ∶ A ∋ x
  left  : ∀ {Γ Δ x}               → Γ         ∋ x → Γ ++ Δ    ∋ x
  right : ∀ {Γ Δ x}               → Δ         ∋ x → Γ ++ Δ    ∋ x

infix 4 _∋?_
_∋?_ : (Γ : Session) → (x : Chan) → Dec (Γ ∋ x)
Γ , y ∶ A ∋? x with x ≟Chan y
... | yes x≈y = yes (here x≈y)
... | no ¬x≈y with Γ ∋? x
... | yes Γ∋x = yes (there ¬x≈y Γ∋x)
... | no ¬Γ∋x = no (λ where (here x≈y) → ¬x≈y x≈y
                            (there _ Γ∋x) → ¬Γ∋x Γ∋x)
(Γ ++ Δ) ∋? x with Γ ∋? x 
... | yes Γ∋x = yes (left Γ∋x)
... | no ¬Γ∋x with Δ ∋? x 
... | yes Δ∋x = yes (right Δ∋x)
... | no ¬Δ∋x = no (λ where (left Γ∋x) → ¬Γ∋x Γ∋x
                            (right Δ∋x) → ¬Δ∋x Δ∋x)
∅ ∋? x = no (λ ())

open import Data.Product hiding (swap)
open import Data.Empty using (⊥-elim)

infix 4 _≈_
_≈_ : Session → Session → Set a
Γ ≈ Δ = ∀ x → (Γ ∋ x → Δ ∋ x) × (Δ ∋ x → Γ ∋ x)

∅∌x : ∀ {x} → ¬ ∅ ∋ x
∅∌x ()

open DecSetoid ChanSetoid hiding (_≈_)

∅-empty : ∀ {Δ x A} → ¬ ∅ ≈ Δ , x ∶ A
∅-empty {Δ} {x} P with P x
... | fst , snd = ∅∌x (snd (here refl))

swap : ∀ {Γ x y z A B} → Γ , x ∶ A , y ∶ B ∋ z → Γ , y ∶ B , x ∶ A ∋ z
swap {y = y} (here z≈y) = there {!   !} (here z≈y)
swap (there x P) = {!   !}

lookup : (Γ : Session) (x : Chan) → Dec (∃[ Δ ] ∃[ A ] (Γ ≈ (Δ , x ∶ A)))
lookup (Γ , y ∶ A) x with x ≟Chan y
... | yes x≈y = yes (Γ , A , λ v → (λ where (here v≈y) → here (trans v≈y (sym x≈y))
                                            (there v≉y Γ∋v) → there (λ v≈x → v≉y (trans v≈x x≈y)) Γ∋v)
                                  , λ where (here v≈x) → here (trans v≈x x≈y)
                                            (there v≉x Γ∋v) → there (λ v≈y → v≉x (trans v≈y (sym x≈y))) Γ∋v) 
... | no ¬x≈y with lookup Γ x 
... | yes (Δ , B , Γ≈Δ,x∶B) = yes (Δ , y ∶ A , B , λ v → (λ where (here v≈y) → there (λ v≈x → ¬x≈y (trans (sym v≈x) v≈y)) (here v≈y)
                                                                  (there _ Γ∋v) → {! proj₁ (Γ≈Δ,x∶B v)  !})
                                                                    -- lemma-1 (proj₁ (Γ≈Δ,x∶B v) Γ∋v)) 
                                                        , λ where (here v≈x) → there (λ v≈y → ¬x≈y (trans (sym v≈x) v≈y)) (proj₂ (Γ≈Δ,x∶B v) (here v≈x))
                                                                  (there _ Δ,y∶A∋y) → ,-weakening y A (proj₂ (Γ≈Δ,x∶B v)) (lemma-1 Δ,y∶A∋y))
    where 
      

      lemma-1 : ∀ {Γ x y z A B} → Γ , x ∶ A ∋ z → Γ , y ∶ B , x ∶ A ∋ z
      lemma-1 (here z≈x) = here z≈x
      lemma-1 (there z≉x Γ∋z) = there z≉x (there {!  !} Γ∋z)

      ,-weakening : ∀ {Γ Δ v} x A → (Γ ∋ v → Δ ∋ v) → (Γ , x ∶ A ∋ v → Δ , x ∶ A ∋ v)
      ,-weakening x A f (here v≈x) = here v≈x
      ,-weakening x A f (there v≉x Γ∋v) = there v≉x (f Γ∋v)

... | no ¬P = no (λ where (Δ , B , Q) → ¬P (Δ , B , λ v → (λ where 
                                                              (here P) → proj₁ (Q v) (there {!   !} (here P))
                                                              (there _ P) → proj₁ (Q v) (there {!   !} (there {!   !} P))
                                                              (left P) → proj₁ (Q v) (there {!   !} (left P))
                                                              (right P) → proj₁ (Q v) (there {!   !} (right P))) 
                                                                , λ where (here P) → strengthen (proj₂ (Q v) (here P)) (λ y≈v → ¬x≈y (sym (trans y≈v P)))
                                                                          (there v≉x P) → temp Δ B v v≉x P (proj₂ (Q v))))
    where 
      strengthen : ∀ {Γ x A v} → Γ , x ∶ A ∋ v → x ≉ v → Γ ∋ v
      strengthen (here x≈v) x≉v = ⊥-elim (x≉v (sym x≈v))
      strengthen (there _ P) x≉v = P


      temp : ∀ Δ B v → v ≉ x → (Δ ∋ v) → (f : Δ , x ∶ B ∋ v → Γ , y ∶ A ∋ v) → Γ ∋ v
      temp Δ B v v≉x Δ∋v f = {! f (there ? ?) !}
      -- with v ≟Chan x
      -- ... | yes v≈x = strengthen (f (here v≈x)) (λ y≈v → ¬x≈y (sym (trans y≈v v≈x)))
      -- ... | no ¬v≈x with y ≟Chan v
      -- ... | yes y≈v = {!   !}
      -- ... | no ¬y≈v = strengthen (f (there {!   !} Δ∋v)) ¬y≈v
lookup (Γ ++ Δ) x = {!   !}
lookup ∅ x = no (λ where (Δ , A , P) → ∅-empty P)

-- -- _≈?_ : (Γ Δ : Session) → Dec (Γ ≈ Δ)
-- -- Γ ≈? Δ = {!   !}
-- -- empty : ∀ {Γ x A} → ¬ (∅ ≈ (Γ , x ∶ A))
-- -- empty {Γ} {x} {A} P with x ≟ x
-- -- ... | no ¬p = {!   !}
-- -- ... | yes p = {!   !}

-- -- lookup : (Γ : Session) (x : Chan) → Dec (∃[ Δ ] ∃[ A ] (Γ ≈ (Δ , x ∶ A)))
-- -- lookup (Γ , y ∶ A) x = {!   !}
-- -- lookup (Γ ++ Δ) x with lookup Γ x 
-- -- ... | yes p = {!   !}
-- -- ... | no ¬p = {!   !}
-- -- lookup ∅ x = no (λ where (Γ , A , P) → {! P x  !})

