module App where 

open import Parallel
import ShiftVar
open import Reasoning

open import Data.Nat

var-lemma : ∀ {m i} x M N 
    →   subst-var (match x (suc (m + i))) N [ M [ N / i ] / m     ] 
    β→* subst-var (match x       m      ) M [ N           / m + i ]
var-lemma {m} {i} x M N with match x (suc m + i)
var-lemma {m} {i} x M N  | Under x<1+m+i with match x m  
... | Under x<m = 
    begin
        var x 
    ≡⟨ {!  !} ⟩ 
        {!   !}
    ≡⟨ {!   !} ⟩ 
        subst-var (match x (m + i)) N
    ∎ 
... | Exact x₂ = {!   !}
... | Above .m v = {!   !}
var-lemma {m} {i} x M N  | Exact x₁ = {!   !}
var-lemma {m} {i} x M N  | Above .(suc (m + i)) v = {!   !}

lemma : ∀ {m i} M N O → M [ O / suc m + i ] [ N [ O / i ] / m ] β→* M [ N / m ] [ O / m + i ]
lemma (var x) N O = {!   !}
lemma (ƛ M)   N O = cong-ƛ (lemma M N O)
lemma (M ∙ L) N O = cong-∙ (lemma M N O) (lemma L N O)