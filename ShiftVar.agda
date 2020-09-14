module ShiftVar where

open import Parallel

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties      

open import Agda.Builtin.Bool

module CMP where 
  open ≤-Reasoning

  m+n≰x+m : ∀ {m n x} → n ≰ x → m + n > x + m
  m+n≰x+m {m} {n} {x} n≰x = begin 
      suc x + m 
    ≡⟨ +-comm (suc x) m ⟩ 
      m + suc x
    ≤⟨ +-monoʳ-≤ m (≰⇒> n≰x) ⟩ 
      m + n 
    ∎

  m+n≤x+m : ∀ {m n x} → n ≤ x → m + n ≤ x + m
  m+n≤x+m {m} {n} {x} n≤x = begin 
      m + n 
    ≤⟨ +-monoʳ-≤ m n≤x ⟩ 
      m + x 
    ≡⟨ +-comm m x ⟩ 
      x + m 
    ∎

open ≡-Reasoning

shift-var-lemma-≤ : ∀ {n i x} → n ≤ x → i + x ≡ shift-var n i x 
shift-var-lemma-≤ {zero}  {i} {x}     cmp       = +-comm i x
shift-var-lemma-≤ {suc n} {i} {suc x} (s≤s cmp) =
    i + suc x
  ≡⟨ +-suc i x ⟩ 
    suc (i + x) 
  ≡⟨ cong suc (shift-var-lemma-≤ cmp) ⟩ 
    suc (shift-var n i x) 
  ∎

shift-var-lemma-> : ∀ {n i x} → n > x → x ≡ shift-var n i x 
shift-var-lemma-> {suc n} {i} {zero}  n>x       = refl
shift-var-lemma-> {suc n} {i} {suc x} (s≤s n>x) = cong suc (shift-var-lemma-> n>x)

shift-var-lemma : ∀ n i x m → shift-var n i x + m ≡ shift-var (m + n) i (x + m)
shift-var-lemma n i x m with n ≤? x
... | true because ofʸ p = 
        shift-var n i x + m 
      ≡⟨ cong (λ w → w + m) (sym (shift-var-lemma-≤ p)) ⟩ 
        i + x + m 
      ≡⟨ +-assoc i x m ⟩ 
        i + (x + m)
      ≡⟨ shift-var-lemma-≤ {m + n} {i} {x + m} (CMP.m+n≤x+m p) ⟩ 
        shift-var (m + n) i (x + m) 
      ∎
... | false because ofⁿ ¬p = 
        shift-var n i x + m 
      ≡⟨ cong (λ w → w + m) (sym (shift-var-lemma-> (≰⇒> ¬p))) ⟩ 
        x + m 
      ≡⟨ shift-var-lemma-> (CMP.m+n≰x+m ¬p) ⟩ 
        shift-var (m + n) i (x + m) 
      ∎

--             shift-var (l + n) i
--        ∙ --------------------------> ∙
--        |                             |
--        |                             |
--   shift-var l m                  shift-var l m
--        |                             |
--        ∨                             ∨           
--        ∙ --------------------------> ∙
--            shift-var (l + m + n) i

shift-var-shift-var : ∀ l m n i x → shift-var l m (shift-var (l + n) i x) ≡ shift-var (l + m + n) i (shift-var l m x)
shift-var-shift-var zero    m n i x       = shift-var-lemma n i x m
shift-var-shift-var (suc l) m n i zero    = refl
shift-var-shift-var (suc l) m n i (suc x) = cong suc (shift-var-shift-var l m n i x)



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
shift-shift l m n i (var x) = cong-var (shift-var-shift-var l m n i x)
shift-shift l m n i (ƛ N) = cong-ƛ (shift-shift (suc l) m n i N)
shift-shift l m n i (M ∙ N) = cong-∙ (shift-shift l m n i M) (shift-shift l m n i N)
