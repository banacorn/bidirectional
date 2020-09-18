module Reasoning where 

open import Base
open import Reduction

open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using (preorder)
open import Relation.Binary.Reasoning.Preorder (preorder _β→_)
open import Relation.Binary.Reasoning.Preorder (preorder _β→_) using (begin_; step-≡; _∎; _≡⟨⟩_) public


infixr 2 _→*⟨_⟩_
_→*⟨_⟩_ : ∀ (x : Term) {y z} → x β→* y → y IsRelatedTo z → x IsRelatedTo z
x →*⟨ P ⟩ y = x ∼⟨ P ⟩ y

infixr 2 _→⟨_⟩_
_→⟨_⟩_ : ∀ (x : Term) {y z} → x β→ y → y IsRelatedTo z → x IsRelatedTo z
x →⟨ P ⟩ y = x ∼⟨ return P ⟩ y

infixr 2 _→⟨⟩_
_→⟨⟩_ : ∀ (x : Term) {y} → x IsRelatedTo y → x IsRelatedTo y
x →⟨⟩ y = x ∼⟨ ε ⟩ y