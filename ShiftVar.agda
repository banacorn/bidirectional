module ShiftVar where

open import Parallel

open import Data.Nat
open import Relation.Nullary 
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties      

open import Agda.Builtin.Bool

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

open ≡-Reasoning

shift-var-lemma-≤ : ∀ {n i x} → n ≤ x → i + x ≡ shift-var n i x 
shift-var-lemma-≤ {n} {i} {x} n≤x with n ≤? x 
... | .true  because ofʸ  p = refl
... | .false because ofⁿ ¬p = contradiction n≤x ¬p

shift-var-lemma-> : ∀ {n i x} → n > x → x ≡ shift-var n i x 
shift-var-lemma-> {n} {i} {x} n>x with n ≤? x 
... | .true  because ofʸ  p = contradiction p (<⇒≱ n>x)
... | .false because ofⁿ ¬p = refl

shift-var-lemma : ∀ n i x m → shift-var n i x + m ≡ shift-var (m + n) i (x + m)
shift-var-lemma n i x m with n ≤? x
... | .true  because ofʸ  p = 
    i + x + m 
  ≡⟨ +-assoc i x m ⟩ 
    i + (x + m) 
  ≡⟨ shift-var-lemma-≤ {m + n} {i} {x + m} (INEQ.m+n≤x+m p) ⟩ 
    shift-var (m + n) i (x + m) 
  ∎
... | false because ofⁿ ¬p = 
    x + m 
  ≡⟨ shift-var-lemma-> (INEQ.m+n≰x+m ¬p) ⟩ 
    shift-var (m + n) i (x + m) 
  ∎

--             shift-var (l + n) i
--        ∙ --------------------------> ∙
--        |                             |
--        |                             |
--   shift-var l m                  shift-var l m
--        |                             |
--        ∨                             ∨           
--        ∙ --------------------------> ∙
--            shift-var (l + m + n) i

shift-var-shift-var : ∀ l m n i x → shift-var l m (shift-var (l + n) i x) ≡ shift-var (l + m + n) i (shift-var l m x)
shift-var-shift-var l m n i x with l ≤? x | l + n ≤? x 
... | yes l≤x | yes l+n≤x = 
    shift-var l m (i + x)
  ≡⟨ sym (shift-var-lemma-≤ ((≤-trans l≤x (m≤n+m x i)))) ⟩ 
    m + (i + x)
  ≡⟨ EQ.twist m i x ⟩ 
    i + (m + x)
  ≡⟨ shift-var-lemma-≤ (INEQ.l+m+n≤m+x l m n x l+n≤x) ⟩ 
    shift-var (l + m + n) i (m + x)
  ∎
... | yes l≤x | no  l+n>x = 
    shift-var l m x
  ≡⟨ sym (shift-var-lemma-≤ l≤x) ⟩ 
    m + x
  ≡⟨ shift-var-lemma-> (INEQ.l+m+n>m+x l m n x (≰⇒> l+n>x)) ⟩ 
    shift-var (l + m + n) i (m + x)
  ∎
... | no  l>x | yes l+n≤x = contradiction (≤-trans (m≤m+n l n) l+n≤x) l>x
... | no  l>x | no  l+n>x = 
    shift-var l m x
  ≡⟨ sym (shift-var-lemma-> (≰⇒> l>x)) ⟩ 
    x
  ≡⟨ shift-var-lemma-> (INEQ.l+m+n>x l m n x (≰⇒> l>x)) ⟩ 
    shift-var (l + m + n) i x
  ∎

-- shift-var-shift-var l m n i x | .false because ofⁿ l>x = {!   !}

-- shift-var-shift-var : ∀ l m n i x → shift-var l m (shift-var (l + n) i x) ≡ shift-var (l + m + n) i (shift-var l m x)
-- shift-var-shift-var zero    m n i x       = shift-var-lemma n i x m
-- shift-var-shift-var (suc l) m n i zero    = refl
-- shift-var-shift-var (suc l) m n i (suc x) = cong suc (shift-var-shift-var l m n i x)



--                shift (l + n) i
--        ∙ --------------------------> ∙
--        |                             |
--        |                             |
--   shift l m                      shift l m
--        |                             |
--        ∨                             ∨           
--        ∙ --------------------------> ∙
--              shift (l + m + n) i

shift-shift : ∀ l m n i N → shift l m (shift (l + n) i N) β→* shift (l + m + n) i (shift l m N)
shift-shift l m n i (var x) = cong-var (shift-var-shift-var l m n i x)
shift-shift l m n i (ƛ N)   = cong-ƛ (shift-shift (suc l) m n i N)
shift-shift l m n i (M ∙ N) = cong-∙ (shift-shift l m n i M) (shift-shift l m n i N)
