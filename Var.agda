module Var where 

open import Parallel
import ShiftVar
open import Reasoning

open import Data.Nat
open import Relation.Nullary 
open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Agda.Builtin.Bool
      
lemma : ∀ n i x N 
    → subst-var (match (shift-var (suc n) i x) 0) (shift n i N) 
  β→* shift n i (subst-var (match x 0) N)
lemma n i zero N = ShiftVar.shift-shift 0 0 n i N
lemma n i (suc x) N = ε
