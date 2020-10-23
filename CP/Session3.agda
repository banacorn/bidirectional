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

seperate : (Γ : Session) → (x : Chan) → Dec (∃[ Δ ] ∃[ A ] (Γ ≋ x ∶ A ∷ Δ))
seperate []          x = no (λ where (Δ , A , fst , snd) → ∉[] snd)
seperate (y ∶ A ∷ Γ) x with y ≟ x 
... | yes p = yes {!   !}
-- ... | yes p = yes (Γ , A , (λ {v} → ⊆-∷-cong p (λ {w} → (⊆-refl {_} {w})) {v}) , λ {v} → λ x₁ → {!   !})
... | no ¬p with seperate Γ x 
... | yes (Δ , B , to , from) = yes (y ∶ A ∷ Δ , B , {!   !})
... | no ¬q = {!   !}

-- infixr 5 _#_
-- _#_ : Session → TypeOf → Session
-- Γ # x∶A with x∶A ∈? Γ 
-- ... | yes p = {!   !}
-- ... | no ¬p = {!   !}

-- Chan : Set
-- Chan = DecSetoid.Carrier ChanSetoid

-- _≟Chan_ = DecSetoid._≟_ ChanSetoid
-- _≈Chan_ = DecSetoid._≈_ ChanSetoid
-- _≉Chan_ = DecSetoid._≉_ ChanSetoid

-- infixl 5 _,_∶_ 
-- data Session : Set a where 
--     _,_∶_ : Session → Chan → Type → Session
--     _++_ : Session → Session → Session
--     ∅ : Session


-- -- open import Data.Bool hiding (_≟_)

-- -- open import Data.Empty 
-- -- open import Data.Unit  
-- open import Relation.Nullary
-- open import Relation.Nullary.Decidable

-- -- open import Relation.Binary.PropositionalEquality


-- infix 4 _∋_
-- data _∋_ : (Γ : Session) → (x : Chan) → Set a where
--   here  : ∀ {Γ x y A} → x ≈Chan y         → Γ , y ∶ A ∋ x
--   there : ∀ {Γ x y A} →             Γ ∋ x → Γ , y ∶ A ∋ x
--   left  : ∀ {Γ Δ x}               → Γ ∋ x → Γ ++ Δ    ∋ x
--   right : ∀ {Γ Δ x}               → Δ ∋ x → Γ ++ Δ    ∋ x

-- infix 4 _∋?_
-- _∋?_ : (Γ : Session) → (x : Chan) → Dec (Γ ∋ x)
-- Γ , y ∶ A ∋? x with x ≟Chan y
-- ... | yes x≈y = yes (here x≈y)
-- ... | no ¬x≈y with Γ ∋? x
-- ... | yes Γ∋x = yes (there Γ∋x)
-- ... | no ¬Γ∋x = no (λ where (here x≈y) → ¬x≈y x≈y
--                             (there Γ∋x) → ¬Γ∋x Γ∋x)
-- (Γ ++ Δ) ∋? x with Γ ∋? x 
-- ... | yes Γ∋x = yes (left Γ∋x)
-- ... | no ¬Γ∋x with Δ ∋? x 
-- ... | yes Δ∋x = yes (right Δ∋x)
-- ... | no ¬Δ∋x = no (λ where (left Γ∋x) → ¬Γ∋x Γ∋x
--                             (right Δ∋x) → ¬Δ∋x Δ∋x)
-- ∅ ∋? x = no (λ ())

-- open import Data.Product hiding (swap)
-- open import Data.Empty using (⊥-elim)

-- infix 4 _≈_
-- _≈_ : Session → Session → Set a
-- Γ ≈ Δ = (∀ x → Γ ∋ x → Δ ∋ x) × (∀ x → Δ ∋ x → Γ ∋ x)

-- ∅∌x : ∀ {x} → ¬ ∅ ∋ x
-- ∅∌x ()

-- open DecSetoid ChanSetoid hiding (_≈_)

-- ∅-empty : ∀ {Δ x A} → ¬ ∅ ≈ Δ , x ∶ A
-- ∅-empty {Δ} {x} (P , Q) = ∅∌x (Q x (here refl))

-- swap : ∀ {Γ x y A B} → Γ , x ∶ A , y ∶ B ≈ Γ , y ∶ B , x ∶ A
-- swap {Γ} {x} {y} {A} {B} = to , from
--   where 
--     to : ∀ v → Γ , x ∶ A , y ∶ B ∋ v → Γ , y ∶ B , x ∶ A ∋ v
--     to v (here P) = there (here P)
--     to v (there (here P)) = here P
--     to v (there (there P)) = there (there P)

--     from : ∀ v → Γ , y ∶ B , x ∶ A ∋ v → Γ , x ∶ A , y ∶ B ∋ v
--     from v (here P) = there (here P)
--     from v (there (here P)) = here P
--     from v (there (there P)) = there (there P)

-- -- contract : ∀ {Γ x y A B} →  → Γ , x ∶ A ≈ Γ
-- -- contract
-- -- strengthen : ∀ {Γ x A v} → Γ , x ∶ A ∋ v → x ≉ v → Γ ∋ v
-- -- strengthen (here x≈v) x≉v = ⊥-elim (x≉v (sym x≈v))
-- -- strengthen (there P) x≉v = P

-- lookup : (Γ : Session) (x : Chan) → Dec (∃[ Δ ] ∃[ A ] (Γ ≈ (Δ , x ∶ A)))
-- lookup (Γ , y ∶ A) x with x ≟Chan y
-- ... | yes x≈y = yes (Γ , A  , (λ where v (here v≈y) → here (trans v≈y (sym x≈y))
--                                        v (there Γ∷y∋v) → there Γ∷y∋v) 
--                              , λ where v (here v≈x) → here (trans v≈x x≈y)
--                                        v (there Γ∷x∋v) → there Γ∷x∋v)
-- ... | no ¬x≈y with lookup Γ x 
-- ... | yes (Δ , B , Γ≈Δ,x∶B) = yes (Δ , y ∶ A , B  , (λ where v (here v≈y) → there (here v≈y)
--                                                              v (there Γ∋v) → proj₁ swap v (there (proj₁ Γ≈Δ,x∶B v Γ∋v))) 
--                                                   , λ where v (here v≈x) → there (proj₂ Γ≈Δ,x∶B v (here v≈x))
--                                                             v (there (here v≈y)) → here v≈y
--                                                             v (there (there Δ∋v)) → there (proj₂ Γ≈Δ,x∶B v (there Δ∋v)))
-- ... | no ¬P = no (λ (Δ , B , Q) → ¬P (Δ , B , {!   !}))
--   -- (λ where v P → proj₁ Q v (there P)) 
--   --                                           , (λ where v P → {! proj₂ Q v P   !})))
-- lookup (Γ ++ Δ) x = {!   !}
-- lookup ∅ x = no (λ where (Δ , A , P) → ∅-empty P)

-- -- ... | yes x≈y = yes (Γ , A , λ v → (λ where (here v≈y) → here (trans v≈y (sym x≈y))
-- --                                             (there Γ∋v) → there Γ∋v) -- (λ v≈x → v≉y (trans v≈x x≈y))
-- --                                   , λ where (here v≈x) → here (trans v≈x x≈y)
-- --                                             (there Γ∋v) → there Γ∋v) -- (λ v≈y → v≉x (trans v≈y (sym x≈y))) 
-- -- ... | no ¬x≈y with lookup Γ x 
-- -- ... | yes (Δ , B , Γ≈Δ,x∶B) = yes (Δ , y ∶ A , B , λ v → (λ where (here v≈y) → there (here v≈y) -- (λ v≈x → ¬x≈y (trans (sym v≈x) v≈y)) 
-- --                                                                   (there Γ∋v) → lemma-1 (proj₁ (Γ≈Δ,x∶B v) Γ∋v)) 
-- --                                                         , λ where (here v≈x) → there (proj₂ (Γ≈Δ,x∶B v) (here v≈x)) -- (λ v≈y → ¬x≈y (trans (sym v≈x) v≈y))
-- --                                                                   (there Δ,y∶A∋y) → ,-weakening y A (proj₂ (Γ≈Δ,x∶B v)) (lemma-1 Δ,y∶A∋y))
-- --     where 
-- --       lemma-1 : ∀ {Γ x y z A B} → Γ , x ∶ A ∋ z → Γ , y ∶ B , x ∶ A ∋ z
-- --       lemma-1 (here z≈x) = here z≈x
-- --       lemma-1 (there Γ∋z) = there (there Γ∋z)

-- --       ,-weakening : ∀ {Γ Δ v} x A → (Γ ∋ v → Δ ∋ v) → (Γ , x ∶ A ∋ v → Δ , x ∶ A ∋ v)
-- --       ,-weakening x A f (here v≈x) = here v≈x
-- --       ,-weakening x A f (there Γ∋v) = there (f Γ∋v)

-- -- ... | no ¬P = no λ Q → {!   !}

-- -- -- GOAL : Γ , y ∶ A ≉ CTX , x ∶ TYPE
-- -- -- ¬P     Γ         ≉ CTX , x : TYPE 



-- --   -- no (λ (Δ , B , Q) → ¬P (Δ , B , {!  Q !}))
-- --   -- λ v → (λ Γ∋v → proj₁ (Q v) (there Γ∋v)) 
-- --   --                                                 , (λ Δ,x∶B∋v → {! proj₂ (Q v) Δ,x∶B∋v  !})))
-- --   --                       → (λ Γ∋v → proj₁ (Q v) (there Γ∋v)) 
-- --   --                       , λ Δ,x∶B∋v → {! (proj₂ (Q v) Δ,x∶B∋v)  !}))
-- --                           -- where 
-- --                           --   (here P)  → strengthen (proj₂ (Q v) (here P)) (λ y≈v → ¬x≈y (sym (trans y≈v P)))
-- --                           --   (there P) → {!   !}))
                                                          
-- --     where 

-- --       -- GOAL : Δ , x ∶ B           →       Γ

-- --       -- Q v :  Δ , x ∶ B          <≈>      Γ , y ∶ A 

-- --       -- -- ¬P Δ A =              Γ   <=>  Δ , x ∶ A       
-- --       --        (x₁ : Carrier) →
-- --       --        Σ (Γ ∋ x₁ → Δ₁ , x ∶ A₁ ∋ x₁) (λ x₂ → Δ₁ , x ∶ A₁ ∋ x₁ → Γ ∋ x₁)))

-- --       strengthen : ∀ {Γ x A v} → Γ , x ∶ A ∋ v → x ≉ v → Γ ∋ v
-- --       strengthen (here x≈v) x≉v = ⊥-elim (x≉v (sym x≈v))
-- --       strengthen (there P) x≉v = P

-- --       temp : ∀ Δ B v → (Δ ∋ v) → (f : Δ , x ∶ B ∋ v → Γ , y ∶ A ∋ v) → Γ ∋ v
-- --       temp Δ B v Δ∋v f with v ≟Chan x
-- --       ... | yes v≈x = strengthen (f (here v≈x)) (λ y≈v → ¬x≈y (sym (trans y≈v v≈x)))
-- --       ... | no ¬v≈x with y ≟Chan v
-- --       ... | yes y≈v = {!   !}
-- --       ... | no ¬y≈v = strengthen (f (there Δ∋v)) ¬y≈v
-- --         -- strengthen (f (there Δ∈v)) λ y≈v → {!   !}

-- --       -- lemma : G 

-- -- lookup (Γ ++ Δ) x = {!   !}
-- -- lookup ∅ x = no (λ where (Δ , A , P) → ∅-empty P)

-- -- -- _≈?_ : (Γ Δ : Session) → Dec (Γ ≈ Δ)
-- -- -- Γ ≈? Δ = {!   !}
-- -- -- empty : ∀ {Γ x A} → ¬ (∅ ≈ (Γ , x ∶ A))
-- -- -- empty {Γ} {x} {A} P with x ≟ x
-- -- -- ... | no ¬p = {!   !}
-- -- -- ... | yes p = {!   !}

-- -- -- lookup : (Γ : Session) (x : Chan) → Dec (∃[ Δ ] ∃[ A ] (Γ ≈ (Δ , x ∶ A)))
-- -- -- lookup (Γ , y ∶ A) x = {!   !}
-- -- -- lookup (Γ ++ Δ) x with lookup Γ x 
-- -- -- ... | yes p = {!   !}
-- -- -- ... | no ¬p = {!   !}
-- -- -- lookup ∅ x = no (λ where (Γ , A , P) → {! P x  !})

