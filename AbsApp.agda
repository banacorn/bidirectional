module AbsApp where 

open import Parallel

import ShiftVar
import CMP

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality hiding (preorder)
open import Data.Nat.Properties
open import Agda.Builtin.Bool

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
shift-shift l m n i (var x) = cong-var (ShiftVar.shift-shift-var-l-m' l m n i x)
shift-shift l m n i (ƛ N) = cong-ƛ (shift-shift (suc l) m n i N)
shift-shift l m n i (M ∙ N) = cong-∙ (shift-shift l m n i M) (shift-shift l m n i N)

from-under : ∀ x m n →  x < suc m → suc (suc (m + n)) > x
from-under x m n (s≤s x≤m) = s≤s (≤-trans x≤m (≤-step (m≤m+n m n)))

from-under-2 : ∀ x m n → x < suc m → suc (m + n) > x
from-under-2 x m n (s≤s x≤m) = s≤s (≤-trans x≤m (m≤m+n m n))

prop-1 : ∀ m n i x → x < suc m → shift-var (suc (suc (m + n))) i x ≡ x
prop-1 m n i x x<1+m = sym (ShiftVar.shift-var-lemma-> {suc (suc (m + n))} {i} {x} (from-under x m n x<1+m))

prop-2 : ∀ m n i x → x < suc m → x ≡ shift-var (suc (m + n)) i x
prop-2 m n i x x<1+m = ShiftVar.shift-var-lemma-> {suc (m + n)} {i} {x} (from-under-2 x m n x<1+m)

prop-3 : ∀ m n i x → x ≡ suc m → shift-var (suc (suc (m + n))) i x ≡ x
prop-3 m n i x x≡1+m = sym (ShiftVar.shift-var-lemma-> {suc (suc (m + n))} {i} {x} (s≤s (≤-trans (≤-reflexive x≡1+m) (s≤s (m≤m+n m n)))))

prop-4 : ∀ m n i v → ¬ v ≤ m + n → shift-var (suc (m + n)) i v ≡ i + v
prop-4 m n i v v≰m+n = sym (ShiftVar.shift-var-lemma-≤ {suc (m + n)} {v} i (≰⇒> v≰m+n))

prop-5 : ∀ m n i v → v ≤ m + n → shift-var (suc (m + n)) i v ≡ v
prop-5 m n i v v≤m+n = sym (ShiftVar.shift-var-lemma-> {suc (m + n)} {i} {v} (s≤s v≤m+n))

prop-6 : ∀ m n i v → ¬ v ≤ m + n → i + v ≥ suc m
prop-6 m n i v v≰m+n = ≤-trans (m+n≤o⇒m≤o (suc m) (≰⇒> v≰m+n)) (m≤n+m v i)

open import Relation.Nullary.Negation using (contradiction)

match-≡ : ∀ m n → (eq : m ≡ n) → match m n ≡ Exact eq
match-≡ m n eq with compare m n 
match-≡ m n eq | less .m k = contradiction eq (m≢1+m+n m)
match-≡ m .m refl | equal .m = refl
match-≡ m n eq | greater .n k = contradiction (sym eq) (m≢1+m+n n)

match-> : ∀ m n → (m≥n : m ≥ n) → match (suc m) n ≡ Above n m
match-> m n m≥n with compare (suc m) n
... | less .(suc m) k = contradiction (s≤s (≤-step (m≤m+n m k))) (≤⇒≯ m≥n)
... | equal .(suc m) = contradiction refl (<⇒≢ m≥n)
... | greater .n k = refl

open import Reasoning

var-lemma : ∀ m n i x M N 
    → subst-var (match (shift-var (suc (suc (m + n))) i x) (suc m)) (shift n i M ∙ shift n i N)
  β→* shift (suc (m + n)) i (subst-var (match x (suc m)) (M ∙ N))
var-lemma m n i x M N with match x (suc m) | inspect (match x) (suc m)
var-lemma m n i x M N | Under x<1+m | [ eq ] = 
      begin 
        subst-var (match (shift-var (suc (suc (m + n))) i x) (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var (match w (suc m)) (shift n i M ∙ shift n i N)) (prop-1 m n i x x<1+m) ⟩ 
        subst-var (match x (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i M ∙ shift n i N)) eq ⟩ 
        subst-var (Under x<1+m) (shift n i M ∙ shift n i N)
      ≡⟨⟩ 
        var x
      ≡⟨ cong var_ (prop-2 m n i x x<1+m) ⟩ 
        shift (suc (m + n)) i (var x)
      ≡⟨⟩ 
        shift (suc (m + n)) i (subst-var (Under x<1+m) (M ∙ N))
      ∎ 
var-lemma m n i x M N | Exact x≡1+m | [ eq ] = 
      begin
        subst-var (match (shift-var (suc (suc (m + n))) i x) (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var (match w (suc m)) (shift n i M ∙ shift n i N)) (prop-3 m n i x x≡1+m) ⟩ 
        subst-var (match x (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i M ∙ shift n i N)) (match-≡ x (suc m) x≡1+m) ⟩ 
        subst-var (Exact x≡1+m) (shift n i M ∙ shift n i N)
      ≡⟨⟩ 
        shift 0 (suc m) (shift n i M ∙ shift n i N)
      ≡⟨⟩
        shift 0 (suc m) (shift n i M) ∙ shift 0 (suc m) (shift n i N)
      →*⟨ cong-∙ (shift-shift zero (suc m) n i M) (shift-shift zero (suc m) n i N) ⟩ 
        shift (suc (m + n)) i (shift 0 (suc m) M) ∙ shift (suc (m + n)) i (shift 0 (suc m) N)
      ∎ 
var-lemma m n i x M N | Above _ v | [ eq ] with m + n ≥? v
... | .true because ofʸ v≤m+n = 
      begin
        subst-var (match (suc (shift-var (suc (m + n)) i v)) (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) (suc m)) (shift n i M ∙ shift n i N)) (prop-5 m n i v v≤m+n) ⟩ 
        subst-var (match (suc v) (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i M ∙ shift n i N)) eq ⟩ 
        subst-var (Above i v) (shift n i M ∙ shift n i N)
      ≡⟨⟩ 
        var v
      ≡⟨ cong var_ (sym (prop-5 m n i v v≤m+n)) ⟩ 
        var shift-var (suc (m + n)) i v
      ∎ 
... | .false because ofⁿ v>m+n =
      begin
        subst-var (match (suc (shift-var (suc (m + n)) i v)) (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var (match (suc w) (suc m)) (shift n i M ∙ shift n i N)) (prop-4 m n i v v>m+n) ⟩ 
        subst-var (match (suc (i + v)) (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i M ∙ shift n i N)) (match-> (i + v) (suc m) (prop-6 m n i v v>m+n)) ⟩  
        subst-var (Above i (i + v)) (shift n i M ∙ shift n i N)
      ≡⟨⟩  
        var (i + v)
      ≡⟨ cong var_ (sym (prop-4 m n i v v>m+n)) ⟩ 
        var shift-var (suc (m + n)) i v
      ∎ 

lemma : ∀ m n i M L N 
    → shift (suc (suc (m + n))) i  M [ shift n i L ∙ shift n i N / suc m ] 
  β→* shift       (suc m + n)   i (M [           L ∙           N / suc m ])
lemma m n i (var x) L N = var-lemma m n i x L N
lemma m n i (ƛ M)   L N = cong-ƛ (lemma (suc m) n i M L N)
lemma m n i (M ∙ K) L N = cong-∙ (lemma m n i M L N) (lemma m n i K L N)
