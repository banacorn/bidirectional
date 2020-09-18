module Confluence where 


open import Base 
open import Subst
open import Reduction

open import Data.Product
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 


β→confluent : ∀ {M N O : Term} → (M β→ N) → (M β→ O) → ∃ (λ P → (N β→* P) × (O β→* P))
β→confluent (β-ƛ-∙ {M} {N}) β-ƛ-∙ = M [ N ] , ε , ε
β→confluent (β-ƛ-∙ {M} {N}) (β-∙-l {N = _} (β-ƛ {N = O} M→O)) = (O [ N ]) , cong-[]-l M→O , return β-ƛ-∙
β→confluent (β-ƛ-∙ {M} {N}) (β-∙-r {N = O} N→O) = M [ O ] , cong-[]-r M N→O , return β-ƛ-∙
β→confluent (β-ƛ M→N) (β-ƛ M→O) with β→confluent M→N M→O 
... | P , N→P , O→P = ƛ P , cong-ƛ N→P , cong-ƛ O→P
β→confluent (β-∙-l {L} (β-ƛ {N = N} M→N)) β-ƛ-∙ = N [ L ] , return β-ƛ-∙ , cong-[]-l M→N
β→confluent (β-∙-l {L} M→N) (β-∙-l  M→O) with β→confluent M→N M→O 
... | P , N→P , O→P = P ∙ L , cong-∙-l N→P , cong-∙-l O→P
β→confluent (β-∙-l {N = N} M→N) (β-∙-r {N = O} L→O) = N ∙ O , cong-∙-r (return L→O) , cong-∙-l (return M→N)
β→confluent (β-∙-r {N = N} M→N) (β-ƛ-∙ {O}) = O [ N ] , return β-ƛ-∙ , cong-[]-r O M→N
β→confluent (β-∙-r {N = N} M→N) (β-∙-l {N = O} L→O) = O ∙ N , cong-∙-l (return L→O) , cong-∙-r (return M→N)
β→confluent (β-∙-r {L} {M} {N} M→N) (β-∙-r {N = O} M→O) with β→confluent M→N M→O 
... | P , N→P , O→P = L ∙ P , cong-∙-r N→P , cong-∙-r O→P


-- β→*-confluent : ∀ {M N O} → (M β→* N) → (M β→* O) → ∃ (λ P → (N β→* P) × (O β→* P))
-- β→*-confluent {O = O} ε M→O = O , M→O , ε
-- β→*-confluent {N = N} M→N ε = N , ε , M→N
-- β→*-confluent {M} {N} {O} (_◅_ {j = L} M→L L→N) (_◅_ {j = K} M→K K→O) with β→confluent M→L M→K 
-- ... | M' , L→M'  , K→M' = {!   !}