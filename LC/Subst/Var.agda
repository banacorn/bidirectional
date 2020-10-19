module LC.Subst.Var where 

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary

--------------------------------------------------------------------------------
-- variable binding 

data Binding : ℕ → ℕ → Set where 
  Free  : ∀ {n x} → (n≤x : n ≤ x) → Binding n x
  Bound : ∀ {n x} → (n>x : n > x) → Binding n x

inspectBinding : ∀ n x → Binding n x
inspectBinding n x with n ≤? x 
... | yes p = Free p
... | no ¬p = Bound (≰⇒> ¬p)


--------------------------------------------------------------------------------
-- lifiting variables

lift-var : (n i x : ℕ) → ℕ 
lift-var n i x with inspectBinding n x
... | Free  _ = i + x      -- free 
... | Bound _ =     x      -- bound 

--------------------------------------------------------------------------------
-- properties of lift-var

open import Relation.Binary.PropositionalEquality hiding ([_])

module EQ where 
    open ≡-Reasoning

    twist : ∀ l m n → l + (m + n) ≡ m + (l + n)
    twist l m n = 
        begin
            l + (m + n)
        ≡⟨ sym (+-assoc l m n) ⟩ 
            l + m + n
        ≡⟨ cong (_+ n) (+-comm l m) ⟩ 
            m + l + n
        ≡⟨ +-assoc m l n ⟩ 
            m + (l + n)
        ∎

    l+m+n≡m+x : ∀ l m n x → l + n ≡ x → l + m + n ≡ m + x
    l+m+n≡m+x l m n x l+n≡x = 
        begin
            l + m + n
        ≡⟨ +-assoc l m n ⟩ 
            l + (m + n)
        ≡⟨ twist l m n ⟩ 
            m + (l + n)
        ≡⟨ cong (m +_) l+n≡x ⟩ 
            m + x
        ∎

module INEQ where 
    open ≤-Reasoning

    m+n≰x+m : ∀ {m n x} → n ≰ x → m + n > x + m
    m+n≰x+m {m} {n} {x} n≰x = begin 
            suc x + m 
        ≡⟨ +-comm (suc x) m ⟩ 
            m + suc x
        ≤⟨ +-monoʳ-≤ m (≰⇒> n≰x) ⟩ 
            m + n 
        ∎

    m+n≤x+m : ∀ {m n x} → n ≤ x → m + n ≤ x + m
    m+n≤x+m {m} {n} {x} n≤x = begin 
            m + n 
        ≤⟨ +-monoʳ-≤ m n≤x ⟩ 
            m + x 
        ≡⟨ +-comm m x ⟩ 
            x + m 
        ∎
    l+n≤n+i+x : ∀ l n i x → l ≤ x → l + n ≤ n + i + x
    l+n≤n+i+x l n i x l≤x = 
        begin
            l + n
        ≤⟨ +-monoˡ-≤ n l≤x ⟩ 
            x + n
        ≤⟨ m≤n+m (x + n) i ⟩ 
            i + (x + n)
        ≡⟨ cong (i +_) (+-comm x n) ⟩ 
            i + (n + x)
        ≡⟨ sym (+-assoc i n x) ⟩ 
            i + n + x
        ≡⟨ cong (_+ x) (+-comm i n) ⟩ 
            n + i + x
        ∎

    l+m+n≤m+x : ∀ l m n x → l + n ≤ x → l + m + n ≤ m + x
    l+m+n≤m+x l m n x l+n≤x = 
        begin
            l + m + n
        ≡⟨ +-assoc l m n ⟩ 
            l + (m + n)
        ≡⟨ EQ.twist l m n ⟩ 
            m + (l + n)
        ≤⟨ +-monoʳ-≤ m l+n≤x ⟩ 
            m + x
        ∎

    l+m+n>m+x : ∀ l m n x → l + n > x → l + m + n > m + x
    l+m+n>m+x l m n x l+n>x = 
        begin
            suc m + x
        ≡⟨ sym (+-suc m x) ⟩ 
            m + suc x
        ≤⟨ +-monoʳ-≤ m l+n>x ⟩ 
            m + (l + n)
        ≡⟨ EQ.twist m l n ⟩ 
            l + (m + n)
        ≡⟨ sym (+-assoc l m n) ⟩ 
            l + m + n
        ∎


    l+m+n>x : ∀ l m n x → l > x → l + m + n > x
    l+m+n>x l m n x l>x = 
        begin
            suc x
        ≤⟨ l>x ⟩ 
            l
        ≤⟨ m≤m+n l m ⟩ 
            l + m
        ≤⟨ m≤m+n (l + m) n ⟩ 
            l + m + n
        ∎

open import Relation.Nullary.Negation using (contradiction)
open ≡-Reasoning

lift-var-≤ : ∀ {n i x} → n ≤ x → lift-var n i x ≡ i + x
lift-var-≤ {n} {i} {x} n≤x with inspectBinding n x 
... | Free  ≤x = refl
... | Bound >x = contradiction n≤x (<⇒≱ >x)


lift-var-> : ∀ {n i x} → n > x → lift-var n i x ≡ x 
lift-var-> {n} {i} {x} n>x with inspectBinding n x 
... | Free  ≤x = contradiction n>x (≤⇒≯ ≤x)
... | Bound >x = refl

-- lift-var-+ : ∀ n i x m → lift-var (m + n) i (x + m) ≡ lift-var n i x + m
-- lift-var-+ n i x m with inspectBinding n x 
-- ... | Bound >x  =
--         lift-var (m + n) i (x + m) 
--     ≡⟨ lift-var-> (INEQ.m+n≰x+m (<⇒≱ >x)) ⟩ 
--         x + m 
--     ∎
-- ... | Free  ≤x  = 
--         lift-var (m + n) i (x + m) 
--     ≡⟨ lift-var-≤ {m + n} {i} {x + m} (INEQ.m+n≤x+m ≤x)  ⟩ 
--         i + (x + m) 
--     ≡⟨ sym (+-assoc i x m) ⟩ 
--         i + x + m
--     ∎


--             lift-var (l + n) i
--        ∙ --------------------------> ∙
--        |                             |
--        |                             |
--   lift-var l m                  lift-var l m
--        |                             |
--        ∨                             ∨           
--        ∙ --------------------------> ∙
--            lift-var (l + m + n) i

lift-var-lift-var : ∀ l m n i x → lift-var l m (lift-var (l + n) i x) ≡ lift-var (l + m + n) i (lift-var l m x)
lift-var-lift-var l m n i x with inspectBinding l x | inspectBinding (l + n) x
... | Free l≤x | Free l+n≤x =
        lift-var l m (i + x)
    ≡⟨ lift-var-≤ (≤-trans l≤x (m≤n+m x i)) ⟩ 
        m + (i + x)
    ≡⟨ EQ.twist m i x ⟩ 
        i + (m + x)
    ≡⟨ sym (lift-var-≤ (INEQ.l+m+n≤m+x l m n x l+n≤x)) ⟩ 
        lift-var (l + m + n) i (m + x)
    ∎
... | Free l≤x | Bound l+n>x = 
        lift-var l m x
    ≡⟨ lift-var-≤ l≤x ⟩ 
        m + x
    ≡⟨ sym (lift-var-> (INEQ.l+m+n>m+x l m n x l+n>x)) ⟩ 
        lift-var (l + m + n) i (m + x)
    ∎
... | Bound l>x | Free l+n≤x = contradiction (≤-trans (m≤m+n l n) l+n≤x) (<⇒≱ l>x)
... | Bound l>x | Bound l+n>x =
        lift-var l m x
    ≡⟨ lift-var-> l>x ⟩ 
        x
    ≡⟨ sym (lift-var-> (INEQ.l+m+n>x l m n x l>x)) ⟩ 
        lift-var (l + m + n) i x
    ∎


--             lift-var l (n + i)
--        ∙ --------------------------> ∙
--        |                             |
--        |                             |
--   lift-var l (n + m + i)      lift-var (l + n) m
--        |                             |
--        ∨                             ∨           
--        ∙ --------------------------> ∙
--            

lift-var-lemma : ∀ l m n i x → lift-var l (n + m + i) x ≡ lift-var (l + n) m (lift-var l (n + i) x)
lift-var-lemma l m n i x with inspectBinding l x 
... | Free n≤x = 
  begin 
      n + m + i + x
  ≡⟨ cong (λ w → w + i + x) (+-comm n m) ⟩ 
      m + n + i + x
  ≡⟨ +-assoc (m + n) i x ⟩ 
      m + n + (i + x)
  ≡⟨ +-assoc m n (i + x) ⟩ 
    m + (n + (i + x))
  ≡⟨ cong (m +_) (sym (+-assoc n i x)) ⟩ 
      m + (n + i + x)
  ≡⟨ sym (lift-var-≤ {l + n} {m} {n + i + x} (INEQ.l+n≤n+i+x l n i x n≤x)) ⟩ 
      lift-var (l + n) m (n + i + x)
  ∎ 
... | Bound n>x =
  begin 
      x
  ≡⟨ sym (lift-var-> {l + n} {m} {x} (≤-trans n>x (m≤m+n l n))) ⟩ 
      lift-var (l + n) m x
  ∎ 


