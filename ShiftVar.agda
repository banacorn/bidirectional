module ShiftVar where

open import Parallel
open import CMP

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties      
open ≡-Reasoning
open import Agda.Builtin.Bool

x+i+j≡x+j+i : ∀ x j {i} → x + i + j ≡ x + j + i
x+i+j≡x+j+i x j {i} = 
    x + i + j
  ≡⟨ +-assoc x i j ⟩ 
    x + (i + j)
  ≡⟨ cong (λ z → x + z) (+-comm i j) ⟩ 
    x + (j + i)
  ≡⟨ sym (+-assoc x j i) ⟩ 
    x + j + i 
  ∎

shift-var-n-0-i : ∀ n i → shift-var n 0 i ≡ i
shift-var-n-0-i zero i = +-identityʳ i
shift-var-n-0-i (suc n) zero = refl
shift-var-n-0-i (suc n) (suc i) = cong suc (shift-var-n-0-i n i)

shift-var-lemma' : ∀ n i x → shift-var n i x + 0 ≡ shift-var n i (x + 0)
shift-var-lemma' n i x = 
    shift-var n i x + zero
  ≡⟨ +-identityʳ (shift-var n i x) ⟩ 
    shift-var n i x
  ≡⟨ cong (shift-var n i) (sym (+-identityʳ x)) ⟩ 
    shift-var n i (x + zero)
  ∎

shift-var-on-site : ∀ n i x → shift-var n 0 (x + i) ≡ shift-var n 0 x + i
shift-var-on-site zero i x = x+i+j≡x+j+i x zero
shift-var-on-site (suc n) i zero = shift-var-n-0-i (suc n) i
shift-var-on-site (suc n) i (suc x) = cong suc (shift-var-on-site n i x)

shift-var-lemma-1 : ∀ n i x → shift-var n i x + 1 ≡ shift-var (1 + n) i (x + 1)
shift-var-lemma-1 zero i zero = +-comm i 1
shift-var-lemma-1 zero i (suc x) = cong suc (x+i+j≡x+j+i x 1)
shift-var-lemma-1 (suc n) i zero = refl
shift-var-lemma-1 (suc n) i (suc x) = cong suc (shift-var-lemma-1 n i x)

shift-shift-var : ∀ m n i x → shift-var m 0 (shift-var n i x) ≡ shift-var n i (shift-var m 0 x)
shift-shift-var zero    zero    i x       = x+i+j≡x+j+i x 0
shift-shift-var zero    (suc n) i x       = shift-var-lemma' (suc n) i x
shift-shift-var (suc m) zero    i x       = shift-var-on-site (suc m) i x
shift-shift-var (suc m) (suc n) i zero    = refl
shift-shift-var (suc m) (suc n) i (suc x) = cong suc (shift-shift-var m n i x)

shift-var-lemma-≡ : ∀ n i x → n ≡ x → i + x ≡ shift-var n i x 
shift-var-lemma-≡ zero    i .0 refl = +-identityʳ i
shift-var-lemma-≡ (suc n) i .(suc n) refl = 
    i + suc n
  ≡⟨ +-suc i n ⟩ 
    suc (i + n) 
  ≡⟨ cong suc (shift-var-lemma-≡ n i n refl) ⟩ 
    suc (shift-var n i n) 
  ∎

shift-var-lemma-≤ : ∀ {n x} i → n ≤ x → i + x ≡ shift-var n i x 
shift-var-lemma-≤ {zero}  {x}     i cmp       = +-comm i x
shift-var-lemma-≤ {suc n} {suc x} i (s≤s cmp) =
    i + suc x
  ≡⟨ +-suc i x ⟩ 
    suc (i + x) 
  ≡⟨ cong suc (shift-var-lemma-≤ i cmp) ⟩ 
    suc (shift-var n i x) 
  ∎

shift-var-lemma-> : ∀ {n i x} → n > x → x ≡ shift-var n i x 
shift-var-lemma-> {suc n} {i} {zero}  n>x       = refl
shift-var-lemma-> {suc n} {i} {suc x} (s≤s n>x) = cong suc (shift-var-lemma-> n>x)

shift-shift-var-l-m'-0' : ∀ n i x m → shift-var n i x + m ≡ shift-var (m + n) i (x + m)
shift-shift-var-l-m'-0' n i x m with n ≤? x
... | true because ofʸ p = 
        shift-var n i x + m 
      ≡⟨ cong (λ w → w + m) (sym (shift-var-lemma-≤ i p)) ⟩ 
        i + x + m 
      ≡⟨ +-assoc i x m ⟩ 
        i + (x + m)
      ≡⟨ shift-var-lemma-≤ {m + n} {x + m} i (CMP.m+n≤x+m p) ⟩ 
        shift-var (m + n) i (x + m) 
      ∎
... | false because ofⁿ ¬p = 
        shift-var n i x + m 
      ≡⟨ cong (λ w → w + m) (sym (shift-var-lemma-> (≰⇒> ¬p))) ⟩ 
        x + m 
      ≡⟨ shift-var-lemma-> (CMP.m+n≰x+m ¬p) ⟩ 
        shift-var (m + n) i (x + m) 
      ∎

shift-shift-var-l-m' : ∀ l m n i x → shift-var l m (shift-var (l + n) i x) ≡ shift-var (l + m + n) i (shift-var l m x)
shift-shift-var-l-m' zero    m n i x       = shift-shift-var-l-m'-0' n i x m
shift-shift-var-l-m' (suc l) m n i zero    = refl
shift-shift-var-l-m' (suc l) m n i (suc x) = cong suc (shift-shift-var-l-m' l m n i x)
