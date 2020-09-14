module Shift where 

open import Parallel
import ShiftVar
open import Reasoning

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Data.Nat.Properties
open import Agda.Builtin.Bool

open import Relation.Nullary.Negation using (contradiction)

subst-var-match-< : ∀ {m n} N → (m<n : m < n) → subst-var (match m n) N β→* var m
subst-var-match-< {m} {n} N m<n with match m n 
... | Under m<n' = ε
... | Exact m≡n  = contradiction m≡n (<⇒≢ m<n)
... | Above _ _ m>n = contradiction m>n (<⇒≱ (≤-step m<n))

subst-var-match-≡ : ∀ {m n} N → (m≡n : m ≡ n) → subst-var {_} {n} (match m n) N β→* shift 0 n N
subst-var-match-≡ {m} {.m} N refl with match m m
... | Under m<m = contradiction refl (<⇒≢ m<m)
... | Exact m≡m = ε
... | Above _ _ m>m = contradiction refl (<⇒≢ m>m)

subst-var-match-> : ∀ {m n} N → (1+m>n : suc m > n) → subst-var (match (suc m) n) N β→* var m
subst-var-match-> {m} {n} N 1+m<n with match (suc m) n 
... | Under m<n = contradiction m<n (<⇒≱ (≤-step 1+m<n))
... | Exact m≡n = contradiction (sym m≡n) (<⇒≢ 1+m<n)
... | Above _ _ m>n = ε

var-lemma : ∀ m n i x N 
    → subst-var (match (shift-var (suc (m + n)) i x) m) (shift n i N)
  β→* shift (m + n) i (subst-var (match x m) N)
var-lemma m n i x N with match x m
... | Under x<m = 
      begin 
        subst-var (match (shift-var (suc (m + n)) i x) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match w m) (shift n i N)) (sym (ShiftVar.shift-var-lemma-> prop1)) ⟩ 
        subst-var (match x m) (shift n i N)
      →*⟨ subst-var-match-< (shift n i N) x<m ⟩ 
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
      →*⟨ subst-var-match-≡ (shift n i N) refl ⟩ 
        shift 0 m (shift n i N)
      →*⟨ ShiftVar.shift-shift 0 m n i N ⟩ 
        shift (m + n) i (shift 0 m N)
      ∎ 
      where 
        prop : suc (m + n) > m
        prop =  s≤s (m≤m+n m n)

... | Above _ v m≤v with <-cmp (m + n) v 
... | tri< m+n<v ¬b ¬c = 
      begin
        subst-var (match (suc (shift-var (m + n) i v)) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) m) (shift n i N)) (sym (ShiftVar.shift-var-lemma-≤ prop)) ⟩ 
        subst-var (match (suc (i + v)) m) (shift n i N)
      →*⟨ subst-var-match-> (shift n i N) (prop2 (suc m) n (suc i) v m+n<v) ⟩  
        var (i + v)
      ≡⟨ cong var_ (ShiftVar.shift-var-lemma-≤ prop) ⟩ 
        var shift-var (m + n) i v
      ∎ 
      where 
        prop : m + n ≤ v 
        prop = <⇒≤ m+n<v

        prop2 : ∀ m n i v → m + n ≤ v → m ≤ i + v 
        prop2 m n i v m+n≤v = ≤-trans (m≤m+n m n) (≤-trans m+n≤v (m≤n+m v i))


... | tri≈ ¬a refl ¬c = 
      begin
        subst-var (match (suc (shift-var (m + n) i (m + n))) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) m) (shift n i N)) prop ⟩ 
        subst-var (match (suc (i + (m + n))) m) (shift n i N)
      →*⟨ subst-var-match-> (shift n i N) (prop2 m n i) ⟩ 
        var (i + (m + n))
      ≡⟨ cong var_ (sym prop) ⟩ 
        var shift-var (m + n) i (m + n)
      ∎
      where 
        prop : shift-var (m + n) i (m + n) ≡ i + (m + n)
        prop = sym (ShiftVar.shift-var-lemma-≤ {i = i} ≤-refl)

        prop2 : ∀ m n i → suc (i + (m + n)) > m 
        prop2 m n i = s≤s (≤-trans (m≤m+n m n) (m≤n+m (m + n) i))

... | tri> ¬a ¬b m+n>v =
      begin
        subst-var (match (suc (shift-var (m + n) i v)) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) m) (shift n i N)) prop ⟩ 
        subst-var (match (suc v) m) (shift n i N)
      →*⟨ subst-var-match-> {v} {m} (shift n i N) m≤v ⟩ 
        var v
      ≡⟨ cong var_ (sym prop) ⟩ 
        var shift-var (m + n) i v
      ∎ 
      where 
        prop : shift-var (m + n) i v ≡ v
        prop = sym (ShiftVar.shift-var-lemma-> m+n>v)

lemma : ∀ {m n i} M N 
    → shift (suc ((m + n))) i M [ shift n i N / m ] 
  β→* shift (m + n) i (M [ N / m ])
lemma (var x) N = var-lemma _ _ _ x N
lemma (ƛ M)   N = cong-ƛ (lemma M N)
lemma (K ∙ M) N = cong-∙ (lemma K N) (lemma M N)
