module AbsAbs where 

open import Parallel
import ShiftVar
import CMP

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties
open import Agda.Builtin.Bool

shift-shift-l-m' : ∀ l m n i N → shift l m (shift (l + n) i N) β→* shift (l + m + n) i (shift l m N)
shift-shift-l-m' l m n i (var x) = cong-var (ShiftVar.shift-shift-var-l-m' l m n i x)
shift-shift-l-m' l m n i (ƛ N) = cong-ƛ (shift-shift-l-m' (suc l) m n i N)
shift-shift-l-m' l m n i (M ∙ N) = cong-∙ (shift-shift-l-m' l m n i M) (shift-shift-l-m' l m n i N)


prop-1 : ∀ n i x k → shift-var (suc (suc (x + k + n))) i x ≡ x
prop-1 n i x k = sym (ShiftVar.shift-var-lemma-> {suc (suc (x + k + n))} {i} {x} CMP.2+x+k+n>x)

prop-2 : ∀ x k → compare x (suc (x + k)) ≡ less x k
prop-2 zero k = refl
prop-2 (suc x) k rewrite prop-2 x k = refl

prop-3 : ∀ m n i → shift-var (suc (m + n)) i m ≡ m
prop-3 m n i = sym (ShiftVar.shift-var-lemma-> {suc (m + n)} {i} {m} (s≤s (m≤m+n m n)))

prop-4 : ∀ m → compare m m ≡ equal m 
prop-4 zero = refl
prop-4 (suc m) rewrite prop-4 m = refl


prop-5 : ∀ m n k i → m + n ≤ m + k → shift-var (m + n) i (m + k) ≡ m + (k + i)
prop-5 m n k i m+n≤m+k = 
    shift-var (m + n) i (m + k) 
  ≡⟨ sym (ShiftVar.shift-var-lemma-≤ i m+n≤m+k) ⟩ 
    i + (m + k) 
  ≡⟨ +-comm i (m + k) ⟩ 
    m + k + i 
  ≡⟨ +-assoc m k i ⟩ 
    m + (k + i) ∎
  where 
    open ≡-Reasoning

prop-6 : ∀ m i k → compare (suc (m + (k + i))) m ≡ greater m (k + i)
prop-6 zero    i k = refl
prop-6 (suc m) i k rewrite prop-6 m i k = refl

prop-7 : ∀ m n k i → m + n ≰ m + k → shift-var (m + n) i (m + k) ≡ m + k
prop-7 m n k i rel = sym (ShiftVar.shift-var-lemma-> {m + n} {i} {m + k} (≰⇒> rel))

prop-8 : ∀ m k → compare (suc (m + k)) m ≡ greater m k
prop-8 zero    k = refl 
prop-8 (suc m) k rewrite prop-8 m k = refl 

var-lemma' : ∀ m n i x N → subst-var (ƛ shift (suc n) i N) (compare (shift-var (suc (suc (m + n))) i x) (suc m)) β→* shift (suc (m + n)) i (subst-var (ƛ N) (compare x (suc m)))
var-lemma' m n i x N = {!   !}

var-lemma : ∀ m n i x N → subst-var (ƛ shift (suc n) i N) (compare (shift-var (suc (suc (m + n))) i x) (suc m)) β→* shift (suc (m + n)) i (subst-var (ƛ N) (compare x (suc m)))
var-lemma m n i x N with compare x (suc m)
... | less    .x       k rewrite prop-1 n i x k 
                              | prop-2 x k 
                              = cong-var (ShiftVar.shift-var-lemma-> {suc (x + k + n)} {i} {x} CMP.1+x+k+n>x)
... | equal   .(suc m)   rewrite prop-3 m n i 
                              | prop-4 m 
                              = cong-ƛ (shift-shift-l-m' 1 (suc m) n i N)
... | greater .(suc m) k with m + n ≤? m + k
... | true because ofʸ p rewrite prop-5 m n k i p
                              | prop-6 m i k = ε
... | false because ofⁿ ¬p rewrite prop-7 m n k i ¬p 
                              | prop-8 m k = ε

lemma  : ∀ m n i M N → shift (suc (suc (m + n))) i M [ ƛ shift (suc n) i N / suc m ] β→* shift (suc m + n) i (M [ ƛ N / suc m ])
lemma  m n i (var x) N = var-lemma m n i x N
lemma  m n i (ƛ M)   N = cong-ƛ (lemma  (suc m) n i M N)
lemma  m n i (L ∙ M) N = cong-∙ (lemma  m n i L N) (lemma  m n i M N) 
