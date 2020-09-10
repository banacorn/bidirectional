module AbsApp where 

open import Parallel
import ShiftVar
import CMP

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties
open import Agda.Builtin.Bool

--                shift (l + n) i
--        N ---------------------------> 
--        |                             |
--        |                             |
--   shift l m                      shift l m
--        |                             |
--        ∨                             ∨           
--         ----------------------------> 
--              shift (l + m + n) i

shift-shift : ∀ l m n i N → shift l m (shift (l + n) i N) β→* shift (l + m + n) i (shift l m N)
shift-shift l m n i (var x) = cong-var (ShiftVar.shift-shift-var-l-m' l m n i x)
shift-shift l m n i (ƛ N) = cong-ƛ (shift-shift (suc l) m n i N)
shift-shift l m n i (M ∙ N) = cong-∙ (shift-shift l m n i M) (shift-shift l m n i N)



var-lemma : ∀ m n i x M N 
            → subst-var (shift n i M ∙ shift n i N) (compare (shift-var (suc (suc (m + n))) i x) (suc m))
          β→* shift (suc (m + n)) i (subst-var (M ∙ N) (compare x (suc m)))
var-lemma m n i x M N = {!   !}


lemma : ∀ m n i M L N → shift (suc (suc (m + n))) i M [ shift n i L ∙ shift n i N / suc m ] β→* shift (suc m + n) i (M [ L ∙ N / suc m ])
lemma m n i (var x) L N = var-lemma m n i x L N
lemma m n i (ƛ M)   L N = cong-ƛ (lemma (suc m) n i M L N)
lemma m n i (M ∙ K) L N = cong-∙ (lemma m n i M L N) (lemma m n i K L N)
