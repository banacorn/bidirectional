
module Example where 

open import Base
open import Subst
open import Reduction
open import Reasoning

test-1 : ((ƛ var 0) ∙ var 0) β→* ((var 0) [ var 0 ])
test-1 = 
  begin 
    (ƛ var 0) ∙ var 0 
  →⟨ β-ƛ-∙ ⟩ 
    (var 0) [ var 0 ] 
  ∎

test-0 : ƛ (ƛ var 0 ∙ var 1) ∙ (ƛ var 0 ∙ var 1) β→* ƛ var 0 ∙ var 0
test-0 = 
    begin
        ƛ (ƛ var 0 ∙ var 1) ∙ (ƛ var 0 ∙ var 1)
    →⟨ β-ƛ β-ƛ-∙ ⟩ 
        ƛ (var 0 ∙ var 1) [ ƛ var 0 ∙ var 1 ]
    →⟨⟩ 
        ƛ (var 0 ∙ var 1) [ ƛ var 0 ∙ var 1 / 0 ]
    →⟨⟩ 
        ƛ (var 0) [ ƛ var 0 ∙ var 1 / 0 ] ∙ (var 1) [ ƛ var 0 ∙ var 1 / 0 ]
    →⟨⟩  
        ƛ lift 0 0 (ƛ var 0 ∙ var 1) ∙ var 0
    →⟨⟩  
        ƛ (ƛ lift 0 0 (var 0 ∙ var 1)) ∙ var 0
    →⟨⟩  
        ƛ (ƛ lift 0 0 (var 0) ∙ lift 0 0 (var 1)) ∙ var 0
    →⟨⟩  
        ƛ ((ƛ var 0 ∙ var 1) ∙ var 0)
    →⟨ β-ƛ β-ƛ-∙ ⟩  
        ƛ (var 0 ∙ var 1) [ var 0 / 0 ]
    →⟨⟩  
        ƛ var 0 ∙ var 0
    ∎ 
    
Z : Term 
Z = ƛ ƛ var 0

SZ : Term 
SZ = ƛ ƛ var 1 ∙ var 0

PLUS : Term 
PLUS = ƛ ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)

test-2 : PLUS ∙ Z ∙ SZ β→* SZ
test-2 = 
  begin
    PLUS ∙ Z ∙ SZ
  →⟨ β-∙-l β-ƛ-∙ ⟩ 
    (ƛ ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 0 ] ∙ SZ
  →⟨⟩ 
    (ƛ ((ƛ ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 1 ])) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 2 ])) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ ((var 3 ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)) [ ƛ ƛ var 0 / 3 ])))) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ (var 3) [ ƛ ƛ var 0 / 3 ] ∙ (var 1) [ ƛ ƛ var 0 / 3 ] ∙ (var 2 ∙ var 1 ∙ var 0) [ ƛ ƛ var 0 / 3 ]))) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ (lift 0 3 (ƛ (ƛ var 0))) ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ (ƛ (ƛ (var 0))) ∙ var 1 ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
  →⟨ β-∙-l (β-ƛ (β-ƛ (β-ƛ (β-∙-l β-ƛ-∙)))) ⟩ 
    (ƛ (ƛ (ƛ (ƛ var 0) [ var 1 / 0 ] ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ (ƛ (var 0) [ var 1 / 1 ]) ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ (ƛ var 0) ∙ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
  →⟨ β-∙-l (β-ƛ (β-ƛ (β-ƛ β-ƛ-∙))) ⟩ 
    (ƛ (ƛ (ƛ (var 0) [ var 2 ∙ var 1 ∙ var 0 / 0 ]))) ∙ SZ
  →⟨⟩ 
    (ƛ (ƛ (ƛ (var 2 ∙ var 1 ∙ var 0)))) ∙ SZ
  →⟨ β-ƛ-∙ ⟩ 
    (ƛ (ƛ (var 2 ∙ var 1 ∙ var 0))) [ SZ / 0 ]
  →⟨⟩ 
    ƛ (ƛ (var 2 ∙ var 1 ∙ var 0) [ SZ / 2 ])
  →⟨⟩ 
    ƛ (ƛ lift 0 2 SZ ∙ var 1 ∙ var 0)
  →⟨⟩ 
    ƛ (ƛ (ƛ ƛ var 1 ∙ var 0) ∙ var 1 ∙ var 0)
  →⟨ β-ƛ (β-ƛ (β-∙-l β-ƛ-∙)) ⟩ 
    ƛ (ƛ (ƛ var 1 ∙ var 0) [ var 1 / 0 ] ∙ var 0)
  →⟨⟩ 
    ƛ (ƛ (ƛ ((var 1 ∙ var 0) [ var 1 / 1 ])) ∙ var 0)
  →⟨⟩ 
    ƛ (ƛ (ƛ ((var 1) [ var 1 / 1 ] ∙ (var 0) [ var 1 / 1 ])) ∙ var 0)
  →⟨⟩ 
    ƛ (ƛ (ƛ (lift 0 1 (var 1) ∙ var 0)) ∙ var 0)
  →⟨⟩ 
    ƛ (ƛ (ƛ (var 2 ∙ var 0)) ∙ var 0)
  →⟨ β-ƛ (β-ƛ β-ƛ-∙) ⟩ 
    ƛ (ƛ (var 2 ∙ var 0) [ var 0 / 0 ])
  →⟨⟩ 
    ƛ (ƛ (var 2) [ var 0 / 0 ] ∙ var 0)
  →⟨⟩ 
    ƛ (ƛ var 1 ∙ var 0)
  ∎