module LC.Subst where 

open import LC.Base 
open import LC.Subst.Var 
open import LC.Subst.Term  
open import LC.Subst.Term public using (lift)

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary


--------------------------------------------------------------------------------
-- substitution

infixl 10 _[_/_]
_[_/_] : Term → Term → ℕ → Term
(var x) [ N / i ] = subst-var (match x i) N
(ƛ M)   [ N / i ] = ƛ (M [ N / suc i ])
(L ∙ M) [ N / i ] = L [ N / i ] ∙ M [ N / i ]

-- substitute the 0th var in M for N
infixl 10 _[_]
_[_] : Term → Term → Term
M [ N ] = M [ N / 0 ]


--------------------------------------------------------------------------------
-- properties regarding substitution



open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Negation using (contradiction)
open ≡-Reasoning

subst-< : ∀ x i N → x < i → (var x) [ N / i ] ≡ var x
subst-< x i N x<i with match x i 
... | Under x<i' = refl
... | Exact x≡i  = contradiction x≡i (<⇒≢ x<i)
... | Above v x≥i = contradiction (≤-step (≤-pred x≥i)) (<⇒≱ x<i)

subst-≡ : ∀ x i N → x ≡ i → (var x) [ N / i ] ≡ lift 0 i N
subst-≡ x i N x≡i with match x i 
... | Under x<i  = contradiction x≡i (<⇒≢ x<i)
... | Exact x≡i' = refl
... | Above v x≥i = contradiction (sym x≡i) (<⇒≢ x≥i)


subst-> : ∀ x i N → suc x > i → (var suc x) [ N / i ] ≡ var x
subst-> x i N x≥i with match (suc x) i 
... | Under x<i = contradiction (≤-pred (≤-step x<i)) (<⇒≱ x≥i)
... | Exact x≡i  = contradiction (sym x≡i) (<⇒≢ x≥i)
... | Above v x≥i' = refl



subst-[]-var : ∀ m n i x N 
  → subst-var (match (lift-var n m x) (n + m + i)) N 
  ≡ lift n m (subst-var (match x (n + i)) N)
subst-[]-var m n i x N with inspectBinding n x 
subst-[]-var m n i x N | Free n≤x with match x (n + i)
subst-[]-var m n i x N | Free n≤x | Under x<n+i =
    begin 
        subst-var (match (m + x) (n + m + i)) N
    ≡⟨ subst-var-match-< {m + x} {n + m + i} N (LC.Subst.Var.INEQ.l+m+n>m+x n m i x x<n+i) ⟩ 
        var (m + x)
    ≡⟨ cong var_ (sym (LC.Subst.Var.lift-var-≤ n≤x)) ⟩ 
        var lift-var n m x
    ∎ 
subst-[]-var m n i x N | Free n≤x | Exact x≡n+i =
    begin 
        subst-var (match (m + x) (n + m + i)) N
    ≡⟨ subst-var-match-≡ {m + x} {n + m + i} N (sym (LC.Subst.Var.EQ.l+m+n≡m+x n m i x (sym x≡n+i))) ⟩ 
        lift 0 (n + m + i) N
    ≡⟨ lift-lemma 0 m n i N ⟩ 
        lift n m (lift 0 (n + i) N)
    ∎ 
subst-[]-var m n i .(suc v) N | Free n≤x | Above v x≥n+i = 
    begin 
        subst-var (match (m + suc v) (n + m + i)) N
    ≡⟨ cong (λ w → subst-var (match w (n + m + i)) N) (+-suc m v) ⟩ 
        subst-var (match (suc m + v) (n + m + i)) N
    ≡⟨ subst-var-match-> {m + v} {n + m + i} N (s≤s (LC.Subst.Var.INEQ.l+m+n≤m+x n m i v (≤-pred x≥n+i))) ⟩ 
        var (m + v)
    ≡⟨ cong var_ (sym (LC.Subst.Var.lift-var-≤ {n} {m} {v} (≤-trans (m≤m+n n i) (≤-pred x≥n+i)))) ⟩ 
        var lift-var n m v
    ∎ 
subst-[]-var m n i x N | Bound n>x =
    begin 
        subst-var (match x (n + m + i)) N
    ≡⟨ subst-var-match-< N (≤-trans n>x (≤-trans (m≤m+n n m) (m≤m+n (n + m) i))) ⟩ 
        var x
    ≡⟨ cong var_ (sym (LC.Subst.Var.lift-var-> n>x)) ⟩ 
        var lift-var n m x
    ≡⟨⟩ 
        lift n m (var x)
    ≡⟨ cong (lift n m) (sym (subst-var-match-< N (≤-trans n>x (m≤m+n n i)))) ⟩ 
        lift n m (subst-var (match x (n + i)) N)
    ∎ 

lemma : ∀ {m n i} M N 
  → lift (suc ((m + n))) i M [ lift n i N / m ] 
  ≡ lift (m + n)         i (M [ N / m ])
lemma {m} {n} {i} (var x) N = LC.Subst.Term.subst-var-lift _ _ _ x N
lemma (ƛ M)   N = cong  ƛ_   (lemma M N)
lemma (K ∙ M) N = cong₂ _∙_  (lemma K N) (lemma M N)


lift-[] : ∀ n m i M N → lift n m (M [ N / n + i ]) ≡ lift n m M [ N / n + m + i ] 
lift-[] n m i (var x) N = sym (subst-[]-var m n i x N)
lift-[] n m i (ƛ M) N = cong ƛ_ (lift-[] (suc n) m i M N)
lift-[] n m i (M ∙ M') N = cong₂ _∙_ (lift-[] n m i M N) (lift-[] n m i M' N)


lift-subst-var : ∀ l m n i x N → n ≥ i → i ≥ m → lift (l + m) (suc n) (var x) [ N / l + i ] ≡ lift (l + m) n (var x)
lift-subst-var l m n i x N n≥i i≥m with inspectBinding (l + m) x 
... | Free l+m≤x = 
  begin 
      subst-var (match (suc (n + x)) (l + i)) N
  ≡⟨ subst-var-match-> {n + x} {l + i} N (s≤s prop) ⟩ 
      var (n + x)
  ∎ 
  where 
    prop : l + i ≤ n + x
    prop = ≤-trans (≤-reflexive (+-comm l i)) (+-mono-≤ n≥i (≤-trans (m≤m+n l m) l+m≤x))

... | Bound l+m>x =
    begin 
        subst-var (match x (l + i)) N
    ≡⟨ subst-var-match-< {x} {l + i} N prop ⟩ 
        var x
    ∎ 
    where 
      prop : x < l + i
      prop = ≤-trans l+m>x (+-monoʳ-≤ l i≥m)

lift-subst : ∀ l m n i M N → n ≥ i → i ≥ m → lift (l + m) (suc n) M [ N / l + i ] ≡ lift (l + m) n M
lift-subst l m n i (var x) N n≥i i≥m = lift-subst-var l m n i x N n≥i i≥m
lift-subst l m n i (ƛ M)   N n≥i i≥m = cong ƛ_ (lift-subst (suc l) m n i M N n≥i i≥m)
lift-subst l m n i (L ∙ M) N n≥i i≥m = cong₂ _∙_ (lift-subst l m n i L N n≥i i≥m) (lift-subst l m n i M N n≥i i≥m)


subst-var-match-[] : ∀ {m i} x M N 
    → subst-var (match x (suc (m + i))) N [ M [ N / i ] / m     ] 
    ≡ subst-var (match x       m      ) M [ N           / m + i ]
subst-var-match-[] {m} {i} x M N with match x m 
... | Under x<m = 
    begin 
        subst-var (match x (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ (cong (_[ M [ N / i ] / m ])) (LC.Subst.Term.subst-var-match-< N (≤-trans x<m (≤-step (m≤m+n m i)))) ⟩ 
        (var x) [ M [ N / i ] / m ]
    ≡⟨ subst-< x m (M [ N / i ]) x<m ⟩ 
        var x
    ≡⟨ sym (LC.Subst.Term.subst-var-match-< N (≤-trans x<m (m≤m+n m i))) ⟩ 
        subst-var (match x (m + i)) N
    ∎ 
... | Exact x≡m =
    begin 
        subst-var (match x (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (LC.Subst.Term.subst-var-match-< N (≤-trans (s≤s (≤-reflexive x≡m)) (s≤s (m≤m+n m i)))) ⟩ 
        (var x) [ M [ N / i ] / m ]
    ≡⟨ subst-≡ x m (M [ N / i ]) x≡m ⟩ 
        lift 0 m (M [ N / i ])
    ≡⟨ lift-[] 0 m i M N ⟩ 
        lift 0 m M [ N / m + i ]
    ∎ 
... | Above v v≥m with match v (m + i) 
... | Under v<m+i = 
    begin 
        subst-var (match (suc v) (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (LC.Subst.Term.subst-var-match-< {suc v} {suc m + i} N (s≤s v<m+i)) ⟩ 
        (var suc v) [ M [ N / i ] / m ]
    ≡⟨ subst-> v m (M [ N / i ]) v≥m ⟩ 
        var v
    ∎ 
... | Exact v≡m+i = 
    begin 
        subst-var (match (suc v) (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (LC.Subst.Term.subst-var-match-≡ {suc v} {suc m + i} N (cong suc v≡m+i)) ⟩ 
        lift 0 (suc m + i) N [ M [ N / i ] / m ]
    ≡⟨ lift-subst 0 0 (m + i) m N (M [ N / i ]) (m≤m+n m i) z≤n ⟩ 
        lift 0 (m + i) N
    ∎ 
... | Above v' v>m+i =
    begin 
        subst-var (match (suc (suc v')) (suc (m + i))) N [ M [ N / i ] / m ]
    ≡⟨ cong (_[ M [ N / i ] / m ]) (LC.Subst.Term.subst-var-match-> {suc v'} {suc m + i} N (s≤s v>m+i)) ⟩ 
        (var (suc v')) [ M [ N / i ] / m ]
    ≡⟨ subst-> v' m (M [ N / i ]) (≤-trans (s≤s (m≤m+n m i)) v>m+i) ⟩ 
        var v'
    ∎ 


subst-lemma : ∀ {m i} M N O 
    → M [ O / suc m + i ] [ N [ O / i ] / m     ] 
    ≡ M [ N /     m     ] [ O           / m + i ]
subst-lemma (var x) N O = subst-var-match-[] x N O
subst-lemma (ƛ M)   N O = cong ƛ_ (subst-lemma M N O)
subst-lemma (M ∙ L) N O = cong₂ _∙_ (subst-lemma M N O) (subst-lemma L N O)