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
  -- (ShiftVar.shift-var-lemma-> {suc (suc (m + n))} {i} {x} (from-under x m n x<1+m))

-- prop-3 : ∀ m n i x → x ≡ suc m → shift-var (suc (suc (m + n))) i x ≡ i + x
-- prop-3 m n i x x≡1+m = sym (ShiftVar.shift-var-lemma-≡ (suc (suc (m + n))) i x {!   !})
  -- (from-under-2 x m n x<1+m)


open import Relation.Nullary.Negation using (contradiction)

match-≡ : ∀ m n → (eq : m ≡ n) → match m n ≡ Exact eq
match-≡ m n eq with compare m n 
match-≡ m n eq | less .m k = contradiction eq (m≢1+m+n m)
match-≡ m .m refl | equal .m = refl
match-≡ m n eq | greater .n k = contradiction (sym eq) (m≢1+m+n n)

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
var-lemma m n i x M N | Above x' | [ eq ]  = {!   !}

lemma : ∀ m n i M L N → shift (suc (suc (m + n))) i M [ shift n i L ∙ shift n i N / suc m ] β→* shift (suc m + n) i (M [ L ∙ N / suc m ])
lemma m n i (var x) L N = var-lemma m n i x L N
lemma m n i (ƛ M)   L N = cong-ƛ (lemma (suc m) n i M L N)
lemma m n i (M ∙ K) L N = cong-∙ (lemma m n i M L N) (lemma m n i K L N)
