module Shift where 

open import Parallel
import ShiftVar
-- open import Reasoning

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Data.Nat.Properties
open import Agda.Builtin.Bool

open import Relation.Nullary.Negation using (contradiction)

subst-var-match-< : ∀ {m n} N → (m<n : m < n) → subst-var (match m n) N ≡ var m
subst-var-match-< {m} {n} N m<n with match m n 
... | Under m<n' = refl
... | Exact m≡n  = contradiction m≡n (<⇒≢ m<n)
... | Above _ m>n = contradiction m>n (<⇒≱ (≤-step m<n))

subst-var-match-≡ : ∀ {m n} N → (m≡n : m ≡ n) → subst-var {_} {n} (match m n) N ≡ shift 0 n N
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
--     shift n                                                  shift (m + n) 
--        |                                                          |
--        ∨                                                          ∨           
--        ∙ --------------------------------------------------------> ∙
--              subst-var (match (shift-var (suc (m + n)) i x) m)

open import Relation.Binary.PropositionalEquality hiding (preorder; [_]) 
open ≡-Reasoning

var-lemma : ∀ m n i x N 
    → subst-var (match (shift-var (suc (m + n)) i x) m) (shift n i N)
    ≡ shift (m + n) i (subst-var (match x m) N)
var-lemma m n i x N with match x m
... | Under x<m = 
    begin 
        subst-var (match (shift-var (suc (m + n)) i x) m) (shift n i N)
    ≡⟨ cong (λ w → subst-var (match w m) (shift n i N)) (sym (ShiftVar.shift-var-lemma-> prop1)) ⟩ 
        subst-var (match x m) (shift n i N)
    ≡⟨ subst-var-match-< (shift n i N) x<m ⟩ 
        var x
    ≡⟨ cong var_ (ShiftVar.shift-var-lemma-> prop2) ⟩ 
        shift (m + n) i (var x)
    ∎ 
    where
      prop1 : suc (m + n) > x
      prop1 = ≤-trans x<m (≤-step (m≤m+n m n))

      prop2 : m + n > x
      prop2 = ≤-trans x<m (m≤m+n m n)

... | Exact refl =
      begin
        subst-var (match (shift-var (suc (m + n)) i m) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match w m) (shift n i N)) (sym (ShiftVar.shift-var-lemma-> prop)) ⟩ 
        subst-var (match m m) (shift n i N)
      ≡⟨ subst-var-match-≡ (shift n i N) refl ⟩ 
        shift 0 m (shift n i N)
      ≡⟨ ShiftVar.shift-shift 0 m n i N ⟩ 
        shift (m + n) i (shift 0 m N)
      ∎ 
      where 
        prop : suc (m + n) > m
        prop =  s≤s (m≤m+n m n)

... | Above v m≤v with inspectBinding (suc m + n) (suc v)
... | Free n≤x =
  begin 
    subst-var (match (i + suc v) m) (shift n i N)
  ≡⟨ cong (λ w → subst-var (match w m) (shift n i N)) (+-suc i v) ⟩ 
    subst-var (match (suc i + v) m) (shift n i N) 
  ≡⟨ subst-var-match-> (shift n i N) prop ⟩ 
    var (i + v) 
  ≡⟨ cong var_ (ShiftVar.shift-var-lemma-≤ prop2) ⟩ 
    var (shift-var (m + n) i v)
  ∎ 
  where 
    prop : suc (i + v) > m
    prop = s≤s (≤-trans (≤-pred m≤v) (m≤n+m v i))

    prop2 : m + n ≤ v 
    prop2 = ≤-pred n≤x
... | Bound n>x =
  begin 
    subst-var (match (suc v) m) (shift n i N)
  ≡⟨ subst-var-match-> {v} {m} (shift n i N) m≤v ⟩ 
    var v
  ≡⟨ cong var_ (ShiftVar.shift-var-lemma-> {m + n} {i} {v} (≤-pred n>x)) ⟩ 
    var (shift-var (m + n) i v)
  ∎


shift-var-123 : ∀ l m n i x → shift-var l (n + m + i) x ≡ shift-var (l + n) m (shift-var l (n + i) x)
shift-var-123 l m n i x with inspectBinding l x 
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
  ≡⟨ ShiftVar.shift-var-lemma-≤ {l + n} {m} {n + i + x} (ShiftVar.INEQ.l+n≤n+i+x l n i x n≤x) ⟩ 
      shift-var (l + n) m (n + i + x)
  ∎ 
... | Bound n>x =
  begin 
      x
  ≡⟨ ShiftVar.shift-var-lemma-> {l + n} {m} {x} (≤-trans n>x (m≤m+n l n)) ⟩ 
      shift-var (l + n) m x
  ∎ 


shift-lemma : ∀ l m n i N → shift l (n + m + i) N ≡ shift (l + n) m (shift l (n + i) N)
shift-lemma l m n i (var x) = cong var_ (shift-var-123 l m n i x)
shift-lemma l m n i (ƛ M)   = cong ƛ_ (shift-lemma (suc l) m n i M)
shift-lemma l m n i (M ∙ N) = cong₂ _∙_ (shift-lemma l m n i M) (shift-lemma l m n i N)

subst-[]-var : ∀ m n i x N 
  → subst-var (match (shift-var n m x) (n + m + i)) N 
  ≡ shift n m (subst-var (match x (n + i)) N)
subst-[]-var m n i x N with inspectBinding n x 
subst-[]-var m n i x N | Free n≤x with match x (n + i)
subst-[]-var m n i x N | Free n≤x | Under x<n+i =
    begin 
        subst-var (match (m + x) (n + m + i)) N
    ≡⟨ subst-var-match-< {m + x} {n + m + i} N (ShiftVar.INEQ.l+m+n>m+x n m i x x<n+i) ⟩ 
        var (m + x)
    ≡⟨ cong var_ (ShiftVar.shift-var-lemma-≤ n≤x) ⟩ 
        var shift-var n m x
    ∎ 
subst-[]-var m n i x N | Free n≤x | Exact x≡n+i =
    begin 
        subst-var (match (m + x) (n + m + i)) N
    ≡⟨ subst-var-match-≡ {m + x} {n + m + i} N (sym (ShiftVar.EQ.l+m+n≡m+x n m i x (sym x≡n+i))) ⟩ 
        shift 0 (n + m + i) N
    ≡⟨ shift-lemma 0 m n i N ⟩ 
        shift n m (shift 0 (n + i) N)
    ∎ 
subst-[]-var m n i .(suc v) N | Free n≤x | Above v x≥n+i = 
    begin 
        subst-var (match (m + suc v) (n + m + i)) N
    ≡⟨ cong (λ w → subst-var (match w (n + m + i)) N) (+-suc m v) ⟩ 
        subst-var (match (suc m + v) (n + m + i)) N
    ≡⟨ subst-var-match-> {m + v} {n + m + i} N (s≤s (ShiftVar.INEQ.l+m+n≤m+x n m i v (≤-pred x≥n+i))) ⟩ 
        var (m + v)
    ≡⟨ cong var_ (ShiftVar.shift-var-lemma-≤ {n} {m} {v} (≤-trans (m≤m+n n i) (≤-pred x≥n+i))) ⟩ 
        var shift-var n m v
    ∎ 
subst-[]-var m n i x N | Bound n>x =
    begin 
        subst-var (match x (n + m + i)) N
    ≡⟨ subst-var-match-< N (≤-trans n>x (≤-trans (m≤m+n n m) (m≤m+n (n + m) i))) ⟩ 
        var x
    ≡⟨ cong var_ (ShiftVar.shift-var-lemma-> n>x) ⟩ 
        var shift-var n m x
    ≡⟨⟩ 
        shift n m (var x)
    ≡⟨ cong (shift n m) (sym (subst-var-match-< N (≤-trans n>x (m≤m+n n i)))) ⟩ 
        shift n m (subst-var (match x (n + i)) N)
    ∎ 

lemma : ∀ {m n i} M N 
  → shift (suc ((m + n))) i M [ shift n i N / m ] 
  ≡ shift (m + n)         i (M [ N / m ])
lemma {m} {n} {i} (var x) N = var-lemma _ _ _ x N
lemma (ƛ M)   N = cong  ƛ_   (lemma M N)
lemma (K ∙ M) N = cong₂ _∙_  (lemma K N) (lemma M N)


shift-[] : ∀ n m i M N → shift n m (M [ N / n + i ]) ≡ shift n m M [ N / n + m + i ] 
shift-[] n m i (var x) N = sym (subst-[]-var m n i x N)
shift-[] n m i (ƛ M) N = cong ƛ_ (shift-[] (suc n) m i M N)
shift-[] n m i (M ∙ M') N = cong₂ _∙_ (shift-[] n m i M N) (shift-[] n m i M' N)