module CMP where

open import Data.Nat
open import Data.Nat.Properties      
open ≤-Reasoning

1+x+k+n>x : ∀ {x k n} → suc (x + k + n) > x
1+x+k+n>x {zero} = s≤s z≤n
1+x+k+n>x {suc x} = s≤s 1+x+k+n>x

2+x+k+n>x : ∀ {x k n} → suc (suc (x + k + n)) > x
2+x+k+n>x {zero}  {k} {n} = s≤s z≤n
2+x+k+n>x {suc x} {k} {n} = s≤s 2+x+k+n>x

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

m+0≤x+m : ∀ m x → m + 0 ≤ x + m
m+0≤x+m m x = begin 
    m + zero 
  ≡⟨ +-identityʳ m ⟩ 
    m 
  ≤⟨ m≤m+n m x ⟩ 
    m + x 
  ≡⟨ +-comm m x ⟩ 
    x + m 
  ∎
