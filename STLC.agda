module STLC where 

open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality

-- infix  4 _⊢_
-- infix  4 _∋_∶_
-- infixl 5 _,_

infixr 7 _⟶_

infix  5 ƛ_
infixl 7 _∙_
-- infix  9 `_
infixl 10 _∶_

-- infix  5 μ_
-- infix  8 `suc_
-- infix  9 S_
-- infix  9 #_


data Type : Set where
  _⟶_ : Type → Type → Type
  ⊤    : Type



data Context : Set
data Term : Set 

infix 4 _∋_∶_
data _∋_∶_ : Context → Term → Type → Set


data Context where
  ∅   : Context
  _,_∶_ : Context → Term → Type → Context

data Term where 
  ‵_ : ∀ {Γ x A} → Γ ∋ x ∶ A → Term 

  ƛ_ : Term → Term 

  _∙_ : Term → Term → Term 

  _∶_ : Term → Type → Term

  tt : Term 

data _∋_∶_ where
  Z : ∀ {Γ x A}
      ---------
    → Γ , x ∶ A ∋ x ∶ A

  S_ : ∀ {Γ x A y B}
    → Γ ∋ x ∶ A
      ---------
    → Γ , y ∶ B ∋ x ∶ A


-- lookup : Context → ℕ → Type
-- lookup (Γ , A) zero     =  A
-- lookup (Γ , _) (suc n)  =  lookup Γ n
-- lookup ∅       _        =  ⊥-elim impossible
--   where postulate impossible : ⊥

-- count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
-- count {Γ , _} zero     =  Z
-- count {Γ , _} (suc n)  =  S (count n)
-- count {∅}     _        =  ⊥-elim impossible
--   where postulate impossible : ⊥

-- -- #_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
-- -- # n  =  ` count n



infix 4 _⊢_⇐_
infix 4 _⊢_⇒_

data _⊢_⇐_ : Context → Term → Type → Set
data _⊢_⇒_ : Context → Term → Type → Set


data _⊢_⇒_ where 

  Var : ∀ {Γ x A}
    → Γ ∋ x ∶ A
    ----------------------------
    → Γ ⊢ x ⇒ A

  Anno : ∀ {Γ e A}
    → Γ ⊢ e ⇐ A
    ----------------------------
    → Γ ⊢ (e ∶ A) ⇒ A


  ⟶E : ∀ {Γ f A e B}
    → Γ ⊢ f ⇒ (A ⟶ B)
    → Γ ⊢ e ⇐ A
    ----------------------------
    → Γ ⊢ f ∙ e ⇒ B

data _⊢_⇐_ where 
  
  Sub : ∀ {Γ e A B}
    → Γ ∋ e ∶ A
    → A ≡ B
    ----------------------------
    → Γ ⊢ e ⇐ B

  ⊤I : ∀ {Γ}
    ----------------------------
    → Γ ⊢ tt ⇐ ⊤

  ⟶I : ∀ {Γ x A e B}
    → (Γ , x ∶ A) ⊢ e ⇐ B
    ----------------------------
    → Γ ⊢ ƛ e ⇐ A ⟶ B

-- data ModeCorrect : Set where 