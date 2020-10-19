module LC.Subst.Term where 

open import LC.Base 
open import LC.Subst.Var 

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary

--------------------------------------------------------------------------------
-- lifting terms

lift : (n i : ℕ) → Term → Term
lift n i (var x) = var (lift-var n i x)
lift n i (ƛ M)   = ƛ lift (suc n) i M
lift n i (M ∙ N) = lift n i M ∙ lift n i N

--------------------------------------------------------------------------------
-- properties of lift

open import Relation.Binary.PropositionalEquality hiding ([_])

--             lift l (n + i)
--        ∙ --------------------------> ∙
--        |                             |
--        |                             |
--   lift l (n + m + i)           lift (l + n) m
--        |                             |
--        ∨                             ∨           
--        ∙ --------------------------> ∙
--            


lift-lemma : ∀ l m n i N → lift l (n + m + i) N ≡ lift (l + n) m (lift l (n + i) N)
lift-lemma l m n i (var x) = cong var_ (LC.Subst.Var.lift-var-lemma l m n i x)
lift-lemma l m n i (ƛ M)   = cong ƛ_ (lift-lemma (suc l) m n i M)
lift-lemma l m n i (M ∙ N) = cong₂ _∙_ (lift-lemma l m n i M) (lift-lemma l m n i N)

--                lift (l + n) i
--        ∙ --------------------------> ∙
--        |                             |
--        |                             |
--   lift l m                      lift l m
--        |                             |
--        ∨                             ∨           
--        ∙ --------------------------> ∙
--              lift (l + m + n) i

lift-lift : ∀ l m n i N → lift l m (lift (l + n) i N) ≡ lift (l + m + n) i (lift l m N)
lift-lift l m n i (var x) = cong var_ (lift-var-lift-var l m n i x)
lift-lift l m n i (ƛ N)   = cong ƛ_ (lift-lift (suc l) m n i N)
lift-lift l m n i (M ∙ N) = cong₂ _∙_ (lift-lift l m n i M) (lift-lift l m n i N)


--------------------------------------------------------------------------------
-- substituting variables 

data Match : ℕ → ℕ → Set where
  Under : ∀ {i x} → x     < i → Match x       i
  Exact : ∀ {i x} → x     ≡ i → Match x       i
  Above : ∀ {i} v → suc v > i → Match (suc v) i

open import Relation.Binary.Definitions

match : (x i : ℕ) → Match x i
match x       i with <-cmp x i 
match x       i | tri< a ¬b ¬c = Under a
match x       i | tri≈ ¬a b ¬c = Exact b
match (suc x) i | tri> ¬a ¬b c = Above x c

subst-var : ∀ {x i} → Match x i → Term → Term 
subst-var {x}     (Under _)     N = var x
subst-var {_} {i} (Exact _)     N = lift 0 i N
subst-var         (Above x _) N = var x

--------------------------------------------------------------------------------
-- properties of subst-var

open import Relation.Nullary.Negation using (contradiction)
open ≡-Reasoning

subst-var-match-< : ∀ {m n} N → (m<n : m < n) → subst-var (match m n) N ≡ var m
subst-var-match-< {m} {n} N m<n with match m n 
... | Under m<n' = refl
... | Exact m≡n  = contradiction m≡n (<⇒≢ m<n)
... | Above _ m>n = contradiction m>n (<⇒≱ (≤-step m<n))

subst-var-match-≡ : ∀ {m n} N → (m≡n : m ≡ n) → subst-var {_} {n} (match m n) N ≡ lift 0 n N
subst-var-match-≡ {m} {.m} N refl with match m m
... | Under m<m = contradiction refl (<⇒≢ m<m)
... | Exact m≡m = refl
... | Above _ m>m = contradiction refl (<⇒≢ m>m)

subst-var-match-> : ∀ {m n} N → (1+m>n : suc m > n) → subst-var (match (suc m) n) N ≡ var m
subst-var-match-> {m} {n} N 1+m<n with match (suc m) n 
... | Under m<n = contradiction m<n (<⇒≱ (≤-step 1+m<n))
... | Exact m≡n = contradiction (sym m≡n) (<⇒≢ 1+m<n)
... | Above _ m>n = refl



--              subst-var (match x                             m)
--        ∙ -------------------------------------------------------> ∙
--        |                                                          |
--        |                                                          |
--     lift n                                                  lift (m + n) 
--        |                                                          |
--        ∨                                                          ∨           
--        ∙ --------------------------------------------------------> ∙
--              subst-var (match (lift-var (suc (m + n)) i x) m)

open import Relation.Binary.PropositionalEquality hiding (preorder; [_]) 
open ≡-Reasoning

subst-var-lift : ∀ m n i x N 
    → subst-var (match (lift-var (suc (m + n)) i x) m) (lift n i N)
    ≡ lift (m + n) i (subst-var (match x m) N)
subst-var-lift m n i x N with match x m
... | Under x<m = 
    begin 
        subst-var (match (lift-var (suc (m + n)) i x) m) (lift n i N)
    ≡⟨ cong (λ w → subst-var (match w m) (lift n i N)) (LC.Subst.Var.lift-var-> prop1) ⟩ 
        subst-var (match x m) (lift n i N)
    ≡⟨ subst-var-match-< (lift n i N) x<m ⟩ 
        var x
    ≡⟨ cong var_ (sym (LC.Subst.Var.lift-var-> prop2)) ⟩ 
        lift (m + n) i (var x)
    ∎ 
    where
      prop1 : suc (m + n) > x
      prop1 = ≤-trans x<m (≤-step (m≤m+n m n))

      prop2 : m + n > x
      prop2 = ≤-trans x<m (m≤m+n m n)

... | Exact refl =
      begin
        subst-var (match (lift-var (suc (m + n)) i m) m) (lift n i N)
      ≡⟨ cong (λ w → subst-var (match w m) (lift n i N)) (LC.Subst.Var.lift-var-> prop) ⟩ 
        subst-var (match m m) (lift n i N)
      ≡⟨ subst-var-match-≡ (lift n i N) refl ⟩ 
        lift 0 m (lift n i N)
      ≡⟨ lift-lift 0 m n i N ⟩ 
        lift (m + n) i (lift 0 m N)
      ∎ 
      where 
        prop : suc (m + n) > m
        prop =  s≤s (m≤m+n m n)

... | Above v m≤v with inspectBinding (suc m + n) (suc v)
... | Free n≤x =
  begin 
    subst-var (match (i + suc v) m) (lift n i N)
  ≡⟨ cong (λ w → subst-var (match w m) (lift n i N)) (+-suc i v) ⟩ 
    subst-var (match (suc i + v) m) (lift n i N) 
  ≡⟨ subst-var-match-> (lift n i N) prop ⟩ 
    var (i + v) 
  ≡⟨ cong var_ (sym (LC.Subst.Var.lift-var-≤ prop2)) ⟩ 
    var (lift-var (m + n) i v)
  ∎ 
  where 
    prop : suc (i + v) > m
    prop = s≤s (≤-trans (≤-pred m≤v) (m≤n+m v i))

    prop2 : m + n ≤ v 
    prop2 = ≤-pred n≤x
... | Bound n>x =
  begin 
    subst-var (match (suc v) m) (lift n i N)
  ≡⟨ subst-var-match-> {v} {m} (lift n i N) m≤v ⟩ 
    var v
  ≡⟨ cong var_ (sym (LC.Subst.Var.lift-var-> {m + n} {i} {v} (≤-pred n>x))) ⟩ 
    var (lift-var (m + n) i v)
  ∎

