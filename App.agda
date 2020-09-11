module App where 

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
    
prop-1 : ∀ m n i x → x < m → shift-var (suc (m + n)) i x ≡ x
prop-1 m n i x x<m = sym (ShiftVar.shift-var-lemma-> {suc (m + n)} {i} {x} (≤-trans x<m (≤-step (m≤m+n m n))))

prop-2 : ∀ m n i x → x < m → x ≡ shift-var ((m + n)) i x
prop-2 m n i x x<m = ShiftVar.shift-var-lemma-> {m + n} {i} {x} (≤-trans x<m (m≤m+n m n))

prop-3 : ∀ m n i → shift-var (suc (m + n)) i m ≡ m
prop-3 m n i = sym (ShiftVar.shift-var-lemma-> {suc (m + n)} {i} {m} (s≤s (m≤m+n m n)))

prop-Above-tri< : ∀ m n i v → m + n < v → shift-var (m + n) i v ≡ i + v
prop-Above-tri< m n i v m+n<v = sym (ShiftVar.shift-var-lemma-≤ {m + n} {v} i (<⇒≤ m+n<v))

prop-Above-tri≡ : ∀ m n i → shift-var (m + n) i (m + n) ≡ i + (m + n)
prop-Above-tri≡ m n i = sym (ShiftVar.shift-var-lemma-≤ {m + n} {m + n} i ≤-refl)

prop-Above-tri> : ∀ m n i v → m + n > v → shift-var (m + n) i v ≡ v
prop-Above-tri> m n i v m+n>v = sym (ShiftVar.shift-var-lemma-> {m + n} {i} {v} m+n>v)

open import Relation.Nullary.Negation using (contradiction)

match-≡ : ∀ m → match m m ≡ Exact refl
match-≡ m with <-cmp m m 
... | tri< a ¬b ¬c = contradiction refl ¬b
... | tri≈ ¬a refl ¬c = refl
... | tri> ¬a ¬b c = contradiction refl ¬b

match-Above-tri< : ∀ m n i v → m + n < v → match (suc (i + v)) m ≡ Above m (i + v)
match-Above-tri< m n i v m+n<v with <-cmp (suc i + v) m  
... | tri< a ¬b ¬c = contradiction (≤-trans (m≤m+n m n) (≤-trans (≤-pred (≤-step m+n<v)) (≤-step (m≤n+m v i)))) (<⇒≱ a)
... | tri≈ ¬a refl ¬c = contradiction (≤-step (≤-trans (m≤n+m v i) (m≤m+n (i + v) n))) (<⇒≱ m+n<v)
... | tri> ¬a ¬b c = refl

match-Above-tri≡ : ∀ m n i → match (suc (i + (m + n))) m ≡ Above m (i + (m + n))
match-Above-tri≡ m n i with <-cmp (suc (i + (m + n))) m
... | tri< a ¬b ¬c = contradiction (s≤s (≤-step (≤-trans (m≤m+n m n) (m≤n+m (m + n) i)))) (≤⇒≯ a)
... | tri≈ ¬a b ¬c = contradiction (s≤s (≤-trans (m≤m+n m n) (m≤n+m (m + n) i))) (≤⇒≯ (≤-reflexive b))
... | tri> ¬a ¬b c = refl

var-lemma : ∀ m n i x N 
    → subst-var (match (shift-var (suc (m + n)) i x) m) (shift n i N)
  β→* shift (m + n) i (subst-var (match x m) N)
var-lemma m n i x N with match x m | inspect (match x) m
... | Under x<m | [ eq ] = 
      begin 
        subst-var (match (shift-var (suc (m + n)) i x) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match w m) (shift n i N)) (prop-1 m n i x x<m) ⟩ 
        subst-var (match x m) (shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i N)) eq ⟩ 
        subst-var (Under x<m) (shift n i N)
      ≡⟨⟩ 
        var x
      ≡⟨ cong var_ (prop-2 m n i x x<m) ⟩ 
        shift (m + n) i (var x)
      ≡⟨⟩ 
        shift (m + n) i (subst-var (Under x<m) N)
      ∎ 
... | Exact refl | [ eq ] = 
      begin
        subst-var (match (shift-var (suc (m + n)) i m) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match w m) (shift n i N)) (prop-3 m n i) ⟩ 
        subst-var (match m m) (shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i N)) (match-≡ m) ⟩ 
        subst-var (Exact refl) (shift n i N)
      ≡⟨⟩ 
        shift 0 m (shift n i N)
      →*⟨ ShiftVar.shift-shift 0 m n i N ⟩ 
        shift (m + n) i (shift 0 m N)
      ∎ 
... | Above _ v   | [ eq ] with <-cmp (m + n) v 
... | tri< m+n<v ¬b ¬c = 
      begin
        subst-var (match (suc (shift-var (m + n) i v)) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) m) (shift n i N)) (prop-Above-tri< m n i v m+n<v) ⟩ 
        subst-var (match (suc (i + v)) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i N)) (match-Above-tri< m n i v m+n<v) ⟩  
        subst-var (Above m (i + v)) (shift n i N)
      ≡⟨⟩  
        var (i + v)
      ≡⟨ cong var_ (sym (prop-Above-tri< m n i v m+n<v)) ⟩ 
        var shift-var (m + n) i v
      ∎ 
... | tri≈ ¬a refl ¬c = 
      begin
        subst-var (match (suc (shift-var (m + n) i (m + n))) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) m) (shift n i N)) (prop-Above-tri≡ m n i) ⟩ 
        subst-var (match (suc (i + (m + n))) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i N)) (match-Above-tri≡ m n i) ⟩ 
        subst-var (Above m (i + (m + n))) (shift n i N)
      ≡⟨⟩ 
        var (i + (m + n))
      ≡⟨ cong var_ (sym (prop-Above-tri≡ m n i)) ⟩ 
        var shift-var (m + n) i (m + n)
      ∎
... | tri> ¬a ¬b m+n>v = 
      begin
        subst-var (match (suc (shift-var (m + n) i v)) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) m) (shift n i N)) (prop-Above-tri> m n i v m+n>v) ⟩ 
        subst-var (match (suc v) m) (shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i N)) eq ⟩ 
        subst-var (Above i v) (shift n i N)
      ≡⟨⟩ 
        var v
      ≡⟨ cong var_ (sym (prop-Above-tri> m n i v m+n>v)) ⟩ 
        var shift-var (m + n) i v
      ∎ 


lemma : ∀ m n i M N 
    → shift (suc ((m + n))) i M [ shift n i N / m ] 
  β→* shift (m + n) i (M [ N / m ])
lemma m n i (var x) N = var-lemma m n i x N
lemma m n i (ƛ M)   N = cong-ƛ (lemma (suc m) n i M N)
lemma m n i (K ∙ M) N = cong-∙ (lemma m n i K N) (lemma m n i M N)
