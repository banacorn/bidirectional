module Abs where 

open import Parallel
import ShiftVar
import App

open import Data.Nat

lemma  : ∀ m n i M N → shift (suc (suc (m + n))) i M [ shift n i N / suc m ] β→* shift (suc m + n) i (M [ N / suc m ])
lemma  m n i (var x) N = App.var-lemma (suc m) n i x N
lemma  m n i (ƛ M)   N = cong-ƛ (lemma  (suc m) n i M N)
lemma  m n i (L ∙ M) N = cong-∙ (lemma  m n i L N) (lemma m n i M N) 
