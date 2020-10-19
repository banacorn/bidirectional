module CP where 

open import Data.Nat
open import Relation.Nullary 
open import Data.String using (String)


TypeVar : Set 
TypeVar = String

infixl 11 _^
infixl 10 _⨂_
data Type : Set where 
    ‵_ : TypeVar → Type
    _^ : Type → Type 
    _⨂_ : Type → Type → Type  
    _⅋_ : Type → Type → Type  
    _⨁_ : Type → Type → Type  
    _&_ : Type → Type → Type  
    !_ : Type → Type  
    ¿_ : Type → Type  
    ∃[_] : Type → Type  
    ∀[_] : Type → Type  
    𝟙 : Type 
    ⊥ : Type 
    𝟘 : Type 
    ⊤ : Type 


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

Channel : Set 
Channel = ℕ

infixl 5 _,_∶_ 
data Session : Set where 
    _,_∶_ : Session → Channel → Type → Session
    _++_ : Session → Session → Session
    ∅ : Session





-- infixl 4 _∶_∈_
-- data _∶_∈_ : Channel → Type → Session → Set where
--   Z  : ∀ {Γ x A} 
--     ------------------
--     → x ∶ A ∈ Γ , x ∶ A

--   S_ : ∀ {Γ x y A B} 
--     → x ∶ A ∈ Γ 
--     ------------------
--     → x ∶ A ∈ Γ , x ∶ A , y ∶ B

¿[_] : Session → Session
¿[ Γ , x ∶ A ]  = ¿[ Γ ] , x ∶ ¿ A
¿[ Γ ++ Δ ]     = ¿[ Γ ] ++ ¿[ Δ ]
¿[ ∅ ]          = ∅ 

infix 4 ⊢_
data ⊢_ : Session → Set where  

    Ax : ∀ {A w x} 
        ---------------------------
        → ⊢ ∅ , w ∶ A ^ , x ∶ A

    Cut : ∀ {Γ Δ x A} 
        → (P : ⊢ Γ , x ∶ A) 
        → (Q : ⊢ Δ , x ∶ A ^) 
        ---------------------------
        → ⊢ Γ ++ Δ

    Times : ∀ {Γ Δ x y A B} 
        → (P : ⊢ Γ , y ∶ A) 
        → (Q : ⊢ Δ , x ∶ B) 
        ---------------------------
        → ⊢ Γ ++ Δ , x ∶ A ⨂ B

    Par : ∀ {Θ x y A B} 
        → (R : ⊢ Θ , y ∶ A , x ∶ B) 
        ---------------------------
        → ⊢ Θ , x ∶ A ⅋ B

    PlusL : ∀ {Γ x A B} 
        → (P : ⊢ Γ , x ∶ A) 
        ---------------------------
        → ⊢ Γ , x ∶ A ⨁ B

    PlusR : ∀ {Γ x A B} 
        → (P : ⊢ Γ , x ∶ B) 
        ---------------------------
        → ⊢ Γ , x ∶ A ⨁ B

    With : ∀ {Δ x A B} 
        → (Q : ⊢ Δ , x ∶ A) 
        → (R : ⊢ Δ , x ∶ B) 
        ---------------------------
        → ⊢ Δ , x ∶ A & B

    OfCourse : ∀ {Γ x y A} 
        → (P : ⊢ ¿[ Γ ] , y ∶ A) 
        ---------------------------
        → ⊢ ¿[ Γ ] , x ∶ ! A

    WhyNot : ∀ {Δ x y A} 
        → (Q : ⊢ Δ , y ∶ A) 
        ---------------------------
        → ⊢ Δ , x ∶ ¿ A

    Weaken : ∀ {Δ x A} 
        → (Q : ⊢ Δ) 
        ---------------------------
        → ⊢ Δ , x ∶ ¿ A

    Contract : ∀ {Δ x x' A} 
        → (Q : ⊢ Δ , x ∶ ¿ A , x' ∶ ¿ A) 
        ---------------------------
        → ⊢ Δ , x ∶ ¿ A
    
    -- Exist : ∀ {Γ x x' A} 
    --     → (Q : ⊢ Δ , x ∶ ¿ A , x' ∶ ¿ A) 
    --     ---------------------------
    --     → ⊢ Δ , x ∶ ¿ A