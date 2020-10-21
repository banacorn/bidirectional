module CP where 

open import Data.Nat
open import Relation.Nullary 
-- open import Data.String using (String)


TypeVar : Set 
TypeVar = ℕ 

infixl 10 _⨂_
infixl 10 _⅋_
data Type : Set where 
    -- ‵_ : TypeVar → Type
    -- _^ : Type → Type 
    _⨂_ : Type → Type → Type  
    _⅋_ : Type → Type → Type  
    -- _⨁_ : Type → Type → Type  
    -- _&_ : Type → Type → Type  
    -- !_ : Type → Type  
    -- ¿_ : Type → Type  
    -- ∃[_] : Type → Type  
    -- ∀[_] : Type → Type  
    𝟙 : Type 
    ⊥ : Type 
    𝟘 : Type 
    ⊤ : Type 


infixl 11 _^
_^ : Type → Type 
(A ⨂ B) ^ = A ^ ⅋ B ^
(A ⅋ B) ^ = A ^ ⨂ B ^
𝟙 ^ = ⊥
⊥ ^ = 𝟙
𝟘 ^ = ⊤
⊤ ^ = 𝟘




open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary.Product
open import Data.Product
open import Agda.Builtin.Bool 

-- _≟t_ : (A B : Type) → Dec (A ≡ B)
-- (A ⨂ B) ≟t (C ⨂ D) with A ≟t C | B ≟t D 
-- ... | yes refl | yes refl = yes refl
-- ... | yes refl | no ¬q    = no λ where refl → ¬q refl
-- ... | no ¬p    | yes q    = no λ where refl → ¬p refl
-- ... | no ¬p    | no ¬q    = no λ where refl → ¬p refl
-- (A ⨂ B) ≟t (C ⅋ D) = no (λ ())
-- (A ⨂ B) ≟t 𝟙 = no (λ ())
-- (A ⨂ B) ≟t ⊥ = no (λ ())
-- (A ⨂ B) ≟t 𝟘 = no (λ ())
-- (A ⨂ B) ≟t ⊤ = no (λ ())
-- (A ⅋ B) ≟t (C ⨂ D) = no (λ ())
-- (A ⅋ B) ≟t (C ⅋ D) with A ≟t C | B ≟t D 
-- ... | yes refl | yes refl = yes refl
-- ... | yes refl | no ¬q    = no λ where refl → ¬q refl
-- ... | no ¬p    | yes q    = no λ where refl → ¬p refl
-- ... | no ¬p    | no ¬q    = no λ where refl → ¬p refl
-- (A ⅋ B) ≟t 𝟙 = no (λ ())
-- (A ⅋ B) ≟t ⊥ = no (λ ())
-- (A ⅋ B) ≟t 𝟘 = no (λ ())
-- (A ⅋ B) ≟t ⊤ = no (λ ())
-- 𝟙 ≟t (B ⨂ C) = no (λ ())
-- 𝟙 ≟t (B ⅋ C) = no (λ ())
-- 𝟙 ≟t 𝟙 = yes refl
-- 𝟙 ≟t ⊥ = no (λ ())
-- 𝟙 ≟t 𝟘 = no (λ ())
-- 𝟙 ≟t ⊤ = no (λ ())
-- ⊥ ≟t (B ⨂ C) = no (λ ())
-- ⊥ ≟t (B ⅋ C) = no (λ ())
-- ⊥ ≟t 𝟙 = no (λ ())
-- ⊥ ≟t ⊥ = yes refl
-- ⊥ ≟t 𝟘 = no (λ ())
-- ⊥ ≟t ⊤ = no (λ ())
-- 𝟘 ≟t (B ⨂ C) = no (λ ())
-- 𝟘 ≟t (B ⅋ C) = no (λ ())
-- 𝟘 ≟t 𝟙 = no (λ ())
-- 𝟘 ≟t ⊥ = no (λ ())
-- 𝟘 ≟t 𝟘 = yes refl
-- 𝟘 ≟t ⊤ = no (λ ())
-- ⊤ ≟t (B ⨂ C) = no (λ ())
-- ⊤ ≟t (B ⅋ C) = no (λ ())
-- ⊤ ≟t 𝟙 = no (λ ())
-- ⊤ ≟t ⊥ = no (λ ())
-- ⊤ ≟t 𝟘 = no (λ ())
-- ⊤ ≟t ⊤ = yes refl



Chan : Set 
Chan = ℕ

data Proc⁺ : Set 
data Proc⁻ : Set 

data Proc⁺ where 
    _↔_ : Chan → Chan → Proc⁺

    ν_∶_∙_∣_ : Chan → Type → Proc⁻ → Proc⁻ → Proc⁺
-- infixl  7  _⟦⟧0

-- inherited types
data Proc⁻ where 
    
    -- x[y].(P|Q)
    _⟦_⟧_∣_ : Chan → Chan → Proc⁻ → Proc⁻ → Proc⁻

    -- x(y).(P|Q)
    _⦅_⦆_ : Chan → Chan → Proc⁻ → Proc⁻

    -- x[].0
    _⟦⟧0 : Chan → Proc⁻
    -- x().P
    _⦅⦆_ : Chan → Proc⁻ → Proc⁻
    -- x.case()
    _case : Chan → Proc⁻

-- _[_/_] : Type → Type → TypeVar → Type 
-- (‵ P) [ T / X ] with P ≟ X 
-- ((‵ P) [ T / X ]) | yes p = T
-- ((‵ P) [ T / X ]) | no ¬p = ‵ P
-- (P ^) [ T / X ] = (P [ T / X ]) ^
-- (P ⨂ Q) [ T / X ] = (P [ T / X ]) ⨂ (Q [ T / X ])
-- (P ⅋ Q) [ T / X ] = (P [ T / X ]) ⅋ (Q [ T / X ])
-- (P ⨁ Q) [ T / X ] = (P [ T / X ]) ⨁ (Q [ T / X ])
-- (P & Q) [ T / X ] = (P [ T / X ]) & (Q [ T / X ])
-- (! P) [ T / X ] = ! (P [ T / X ])
-- (¿ P) [ T / X ] = ¿ (P [ T / X ])
-- ∃[ P ] [ T / zero ] = {!   !}
-- ∃[ P ] [ T / suc X ] = {!   !}
-- ∀[ P ] [ T / X ] = {!   !}
-- 𝟙 [ T / X ] = {!   !}
-- ⊥ [ T / X ] = {!   !}
-- 𝟘 [ T / X ] = {!   !}
-- ⊤ [ T / X ] = {!  !}


infixl 5 _,_∶_ 
data Session : Set where 
    _,_∶_ : Session → Chan → Type → Session
    _++_ : Session → Session → Session
    ∅ : Session

infix   4  _⊢↓_
infix   4  _⊢↑_
data _⊢↑_ : Proc⁺ → Session → Set
data _⊢↓_ : Proc⁻ → Session → Set

data _⊢↑_ where 
    ⊢↔ : ∀ {w x A} 
        ---------------
        → w ↔ x ⊢↑ ∅ , w ∶ A ^ , x ∶ A

    ⊢Cut : ∀ {P Q Γ Δ x A} 
        → P ⊢↓ Γ , x ∶ A
        → Q ⊢↓ Δ , x ∶ A ^ 
        ---------------
        → ν x ∶ A ∙ P ∣ Q ⊢↑ Γ ++ Δ 


data _⊢↓_ where 

    ⊢⨂ : ∀ {P Q Γ Δ y x A B}
        → P ⊢↓ Γ , y ∶ A 
        → Q ⊢↓ Δ , x ∶ B
        ---------------
        → x ⟦ y ⟧ P ∣ Q ⊢↓ ∅ , x ∶ 𝟙

    ⊢⅋ : ∀ {R Θ y x A B}
        → R ⊢↓ Θ , y ∶ A , x ∶ B
        ---------------
        → x ⦅ y ⦆ R ⊢↓ Θ , x ∶ A ⅋ B


    ⊢𝟏 : ∀ {x}
        ---------------
        → x ⟦⟧0 ⊢↓ ∅ , x ∶ 𝟙
    
    ⊢⊥ : ∀ {x P Γ}
        → P ⊢↓ Γ 
        ---------------
        → x ⦅⦆ P ⊢↓ Γ , x ∶ ⊥

    ⊢⊤ : ∀ {x Γ}
        ---------------
        → x case ⊢↓ Γ , x ∶ ⊤
 
-- data Result (P : Proc⁺) : Set where 
--     known : (Γ : Session) → P ⊢↑ Γ → Result P
--     cntx? : ((Γ : Session) → P ⊢↑ Γ) → Result P 
--     type? : ((Γ : Session) → (x : Chan) → (T : Type) → P ⊢↑ Γ , x ∶ T) → Result P 
--     wrong : Result P

-- infer : ∀ (P : Proc⁺) → Result P
-- infer (w ↔ x) = type? λ Γ x A → {! ⊢↔ {w} {x} {A} !}
-- infer (ν x ∶ x₁ ∙ x₂ ∣ x₃) = {!   !}

open import Data.Bool hiding (_≟_)

_∋_ : Session → Chan → Bool  
(Γ , y ∶ A) ∋ x with x ≟ y 
... | no ¬p = Γ ∋ x
... | yes p = true
(Γ ++ Δ) ∋ x = (Γ ∋ x) ∨ (Δ ∋ x)
∅ ∋ x = false

_≈_ : Session → Session → Set 
Γ ≈ Δ = ∀ x → Γ ∋ x ≡ Δ ∋ x

empty : ∀ {Γ x A} → ¬ (∅ ≈ (Γ , x ∶ A))
empty {Γ} {x} {A} P with x ≟ x
... | no ¬p = {!   !}
... | yes p = {!   !}

lookup : (Γ : Session) (x : Chan) → Dec (∃[ Δ ] ∃[ A ] (Γ ≈ (Δ , x ∶ A)))
lookup (Γ , y ∶ A) x = {!   !}
lookup (Γ ++ Δ) x with lookup Γ x 
... | yes p = {!   !}
... | no ¬p = {!   !}
lookup ∅ x = no (λ where (Γ , A , P) → {! P x  !})



infer : ∀ (P : Proc⁺) → Dec (∃[ Γ ] (P ⊢↑ Γ))
infer' : ∀ (P : Proc⁻) → Dec (∃[ Γ ] (P ⊢↓ Γ))
check : ∀ (P : Proc⁻) (Γ : Session) → Dec (P ⊢↓ Γ)

infer' (x ⟦ y ⟧ P ∣ Q) = {!   !}
infer' (x ⦅ y ⦆ P) with infer' P 
... | no ¬p = no λ where ((Γ , x ∶ A ⅋ B) , ⊢⅋ P⊢Γ) → ¬p ((Γ , y ∶ A , x ∶ B) , P⊢Γ)
... | yes (Γ , P⊢Γ) = yes ({!   !} , (⊢⅋ {!   !}))
infer' (x ⟦⟧0) = yes (∅ , x ∶ 𝟙 , ⊢𝟏)
infer' (x ⦅⦆ P) with infer' P 
... | no ¬p = no λ where ((Γ , x ∶ ⊥) , ⊢⊥ P⊢Γ) → ¬p (Γ , P⊢Γ)
... | yes (Γ , P⊢Γ) = yes ((Γ , x ∶ ⊥) , (⊢⊥ P⊢Γ))
infer' (x case) = yes (∅ , x ∶ ⊤ , ⊢⊤)

infer (w ↔ x) = yes ((∅ , w ∶ {!   !} , x ∶ {!   !}) , ⊢↔)
infer (ν x ∶ A ∙ P ∣ Q) with infer' P  | infer' Q
... | no ¬p | no ¬q = {!   !}
... | no ¬p | yes q = no (λ where (.(_ ++ _) , ⊢Cut x _) → ¬p {! x  !})
... | yes p | no ¬q = {!   !}
... | yes (Γ , P⊢Γ) | yes (Δ , Q⊢Δ) = yes ({!   !} , ⊢Cut {! P⊢Γ  !} {!   !})
--  = yes ({!   !} , {!   !})

check P Γ = {!   !}


-- infixl 4 _∶_∈_
-- data _∶_∈_ : Channel → Type → Session → Set where
--   Z  : ∀ {Γ x A} 
--     ------------------
--     → x ∶ A ∈ Γ , x ∶ A

--   S_ : ∀ {Γ x y A B} 
--     → x ∶ A ∈ Γ 
--     ------------------
--     → x ∶ A ∈ Γ , x ∶ A , y ∶ B

-- ¿[_] : Session → Session
-- ¿[ Γ , x ∶ A ]  = ¿[ Γ ] , x ∶ ¿ A
-- ¿[ Γ ++ Δ ]     = ¿[ Γ ] ++ ¿[ Δ ]
-- ¿[ ∅ ]          = ∅ 

-- infix 4 ⊢_
-- data ⊢_ : Session → Set where  

--     Ax : ∀ {A w x} 
--         ---------------------------
--         → ⊢ ∅ , w ∶ A ^ , x ∶ A

--     Cut : ∀ {Γ Δ x A} 
--         → (P : ⊢ Γ , x ∶ A) 
--         → (Q : ⊢ Δ , x ∶ A ^) 
--         ---------------------------
--         → ⊢ Γ ++ Δ

--     Times : ∀ {Γ Δ x y A B} 
--         → (P : ⊢ Γ , y ∶ A) 
--         → (Q : ⊢ Δ , x ∶ B) 
--         ---------------------------
--         → ⊢ Γ ++ Δ , x ∶ A ⨂ B

--     Par : ∀ {Θ x y A B} 
--         → (R : ⊢ Θ , y ∶ A , x ∶ B) 
--         ---------------------------
--         → ⊢ Θ , x ∶ A ⅋ B

--     PlusL : ∀ {Γ x A B} 
--         → (P : ⊢ Γ , x ∶ A) 
--         ---------------------------
--         → ⊢ Γ , x ∶ A ⨁ B

--     PlusR : ∀ {Γ x A B} 
--         → (P : ⊢ Γ , x ∶ B) 
--         ---------------------------
--         → ⊢ Γ , x ∶ A ⨁ B

--     With : ∀ {Δ x A B} 
--         → (Q : ⊢ Δ , x ∶ A) 
--         → (R : ⊢ Δ , x ∶ B) 
--         ---------------------------
--         → ⊢ Δ , x ∶ A & B

--     OfCourse : ∀ {Γ x y A} 
--         → (P : ⊢ ¿[ Γ ] , y ∶ A) 
--         ---------------------------
--         → ⊢ ¿[ Γ ] , x ∶ ! A

--     WhyNot : ∀ {Δ x y A} 
--         → (Q : ⊢ Δ , y ∶ A) 
--         ---------------------------
--         → ⊢ Δ , x ∶ ¿ A

--     Weaken : ∀ {Δ x A} 
--         → (Q : ⊢ Δ) 
--         ---------------------------
--         → ⊢ Δ , x ∶ ¿ A

--     Contract : ∀ {Δ x x' A} 
--         → (Q : ⊢ Δ , x ∶ ¿ A , x' ∶ ¿ A) 
--         ---------------------------
--         → ⊢ Δ , x ∶ ¿ A
    
--     -- Exist : ∀ {Γ x x' A} 
--     --     → (Q : ⊢ Δ , x ∶ ¿ A , x' ∶ ¿ A) 
--     --     ---------------------------
--     --     → ⊢ Δ , x ∶ ¿ A