module AbsApp where 

open import Parallel
open import Reasoning
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

-- var-lemma : ∀ m n i x M N 
--             → subst-var (shift n i M ∙ shift n i N) 
--           β→* shift (suc (m + n)) i (subst-var (M ∙ N) (compare x (suc m)))
-- var-lemma m n i x M N = {!   !}

from-under : ∀ x m n →  x ≤ suc m → suc (suc (m + n)) > x
from-under x m n x≤1+m = s≤s (≤-trans x≤1+m (s≤s (m≤m+n m n)))


from-under-2 : ∀ x m n → x ≤ suc m → suc (m + n) > x
from-under-2 x m n x≤1+m = s≤s {!   !}

  -- s≤s (≤-trans x≤1+m (s≤s (m≤m+n m n)))

prop-1 : ∀ m n i x → x ≤ suc m → shift-var (suc (suc (m + n))) i x ≡ x
prop-1 m n i x x≤1+m = sym (ShiftVar.shift-var-lemma-> {suc (suc (m + n))} {i} {x} (from-under x m n x≤1+m))

prop-2 : ∀ m n i x → x ≤ suc m → x ≡ shift-var (suc (m + n)) i x
prop-2 m n i x x≤1+m = ShiftVar.shift-var-lemma-> {suc (m + n)} {i} {x} (from-under-2 x m n x≤1+m)


var-lemma : ∀ m n i x M N 
    → subst-var (match (shift-var (suc (suc (m + n))) i x) (suc m)) (shift n i M ∙ shift n i N)
  β→* shift (suc (m + n)) i (subst-var (match x (suc m)) (M ∙ N))
var-lemma m n i x M N with match x (suc m) | inspect (match x) (suc m)
... | Under x≤1+m | [ eq ] = 
      begin 
        subst-var (match (shift-var (suc (suc (m + n))) i x) (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var (match w (suc m)) (shift n i M ∙ shift n i N)) (prop-1 m n i x x≤1+m) ⟩ 
        subst-var (match x (suc m)) (shift n i M ∙ shift n i N)
      ≡⟨ cong (λ w → subst-var w (shift n i M ∙ shift n i N)) eq ⟩ 
        subst-var (Under x≤1+m) (shift n i M ∙ shift n i N)
      →⟨⟩ 
        var x
      ≡⟨ cong var_ (prop-2 m n i x x≤1+m) ⟩ 
        shift (suc (m + n)) i (var x)
      →⟨⟩ 
        shift (suc (m + n)) i (subst-var (Under x≤1+m) (M ∙ N))
      ∎ 
... | Exact    | [ eq ]  = {!   !}
... | Above x' | [ eq ]  = {!   !}
-- var-lemma : ∀ m n i x M N 
  -- →   subst-var (shift-var (suc (suc (m + n))) i x) (suc m) (shift n i M ∙ shift n i N)
  -- β→* shift (suc (m + n)) i (subst-var x (suc m) (M ∙ N))
-- var-lemma m n i x M N = {!   !}

lemma : ∀ m n i M L N → shift (suc (suc (m + n))) i M [ shift n i L ∙ shift n i N / suc m ] β→* shift (suc m + n) i (M [ L ∙ N / suc m ])
lemma m n i (var x) L N = var-lemma m n i x L N
lemma m n i (ƛ M)   L N = cong-ƛ (lemma (suc m) n i M L N)
lemma m n i (M ∙ K) L N = cong-∙ (lemma m n i M L N) (lemma m n i K L N)
