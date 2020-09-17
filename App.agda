module App where 

open import Parallel
import ShiftVar
import Shift

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality hiding (preorder; [_]) 

open ≡-Reasoning

-- begin 
--     ?
-- ≡⟨ ? ⟩ 
--     ?
-- ≡⟨ ? ⟩ 
--     ?
-- ≡⟨ ? ⟩ 
--     ?
-- ≡⟨ ? ⟩ 
--     ?
-- ∎ 


subst-< : ∀ x i N → x < i → (var x) [ N / i ] ≡ var x
subst-< x i N x<i with match x i 
... | Under x<i' = refl
... | Exact x≡i  = contradiction x≡i (<⇒≢ x<i)
... | Above v x≥i = contradiction (≤-step (≤-pred x≥i)) (<⇒≱ x<i)

subst-≡ : ∀ x i N → x ≡ i → (var x) [ N / i ] ≡ shift 0 i N
subst-≡ x i N x≡i with match x i 
... | Under x<i  = contradiction x≡i (<⇒≢ x<i)
... | Exact x≡i' = refl
... | Above v x≥i = contradiction (sym x≡i) (<⇒≢ x≥i)


subst-> : ∀ x i N → suc x > i → (var suc x) [ N / i ] ≡ var x
subst-> x i N x≥i with match (suc x) i 
... | Under x<i = contradiction (≤-pred (≤-step x<i)) (<⇒≱ x≥i)
... | Exact x≡i  = contradiction (sym x≡i) (<⇒≢ x≥i)
... | Above v x≥i' = refl

var-lemma : ∀ {m i} x M N 
    → subst-var (match x (suc (m + i))) N [ M [ N / i ] / m     ] 
    ≡ subst-var (match x       m      ) M [ N           / m + i ]
var-lemma {m} {i} x M N with match x m 
... | Under x<m = 
    begin 
        subst-var (match x (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ (cong (_[ M [ N / i ] / m ])) (Shift.subst-var-match-< N (≤-trans x<m (≤-step (m≤m+n m i)))) ⟩ 
        (var x) [ M [ N / i ] / m ]
    ≡⟨ subst-< x m (M [ N / i ]) x<m ⟩ 
        var x
    ≡⟨ sym (Shift.subst-var-match-< N (≤-trans x<m (m≤m+n m i))) ⟩ 
        subst-var (match x (m + i)) N
    ∎ 
... | Exact x≡m =
    begin 
        subst-var (match x (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (Shift.subst-var-match-< N (≤-trans (s≤s (≤-reflexive x≡m)) (s≤s (m≤m+n m i)))) ⟩ 
        (var x) [ M [ N / i ] / m ]
    ≡⟨ subst-≡ x m (M [ N / i ]) x≡m ⟩ 
        shift 0 m (M [ N / i ])
    ≡⟨ Shift.shift-[] 0 m i M N ⟩ 
        shift 0 m M [ N / m + i ]
    ∎ 
... | Above v v≥m with match v (m + i) 
... | Under v<m+i = 
    begin 
        subst-var (match (suc v) (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (Shift.subst-var-match-< {suc v} {suc m + i} N (s≤s v<m+i)) ⟩ 
        (var suc v) [ M [ N / i ] / m ]
    ≡⟨ subst-> v m (M [ N / i ]) v≥m ⟩ 
        var v
    ∎ 
... | Exact v≡m+i = 
    begin 
        subst-var (match (suc v) (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (Shift.subst-var-match-≡ {suc v} {suc m + i} N (cong suc v≡m+i)) ⟩ 
        shift 0 (suc m + i) N [ M [ N / i ] / m ]
    ≡⟨ Shift.shift-subst 0 0 (m + i) m N (M [ N / i ]) (m≤m+n m i) z≤n ⟩ 
        shift 0 (m + i) N
    ∎ 
... | Above v' v>m+i =
    begin 
        subst-var (match (suc (suc v')) (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (Shift.subst-var-match-> {suc v'} {suc m + i} N (s≤s v>m+i)) ⟩ 
        (var (suc v')) [ M [ N / i ] / m ]
    ≡⟨ subst-> v' m (M [ N / i ]) (≤-trans (s≤s (m≤m+n m i)) v>m+i) ⟩ 
        var v'
    ∎ 

lemma : ∀ {m i} M N O 
    → M [ O / suc m + i ] [ N [ O / i ] / m     ] 
    ≡ M [ N /     m     ] [ O           / m + i ]
lemma (var x) N O = var-lemma x N O
lemma (ƛ M)   N O = cong ƛ_ (lemma M N O)
lemma (M ∙ L) N O = cong₂ _∙_ (lemma M N O) (lemma L N O)