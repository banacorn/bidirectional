
Intrinsically-typed de Bruijn representation of simply typed lambda calculus
============================================================================

```agda
open import Data.Nat
open import Data.Empty
  hiding (⊥-elim)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  hiding ([_])
```

Fixity declartion
-----------------

```agda
infix  3 _⊢_ _=β_

infixr 7 _→̇_

infixr 5 ƛ_
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infixr 9 ᵒ_ `_ #_
```

Types
-----

We only deal with function types and a ground type ⋆.

```agda
data Type : Set where
  ⋆   : Type
  _→̇_ : Type → Type → Type
```

Context
-------

```agda
infixl 7 _⧺_
infixl 6 _,_
infix  4 _∋_

data Context : Set where
  ∅   :                  Context
  _,_ : Context → Type → Context
```

For convenience, we use symbols

  * `A`, `B`, `C` for types
  * `Γ`, `Δ`, and `Ξ` for contexts

In Agda this convention can be achieved by the keyword `variable` as follows.

```agda
variable
  Γ Δ Ξ : Context
  A B C : Type
```

Membership
----------

`Γ ∋ A` means that A is a member of Γ.

There are two ways of estabilishing the judgement Γ ∋ A.

  1. `Γ , A ∋ A` for any `Γ` and `A`, as we know that `A` is in the
  0-th position.

  2. If `x : Γ ∋ A` is a proof that `A` is in `Γ`, then `Γ , B ∋ A`
     holds.

How should we name these inference rules? Note that if we interpret
the proof of `Γ ∋ A` as the position of `A` in `Γ`, then 1. should be
Z (for zero) and 2. should be S (for successor).

```agda
data _∋_ : Context → Type → Set where
  Z   ---------
    : Γ , A ∋ A

  S_ : Γ     ∋ A
       ---------
     → Γ , B ∋ A

variable
  x     : Γ ∋ A
```

For example, `S Z : ∅ , A , B ∋ A` means `A` is in the first position. That is, 

```agda
_ : ∅ , A , B ∋ A
_ = S Z 
```

Lookup is just `_‼_` in Haskell. Agda is a total language, but
`lookup` can only be partial with this type. We work around this
problem by postulating `⊥`, as we only use `lookup` for examples.

```agda
⊥-elim : ∀ {T : Set} → ⊥ → T
⊥-elim ()

lookup : Context → ℕ → Type
lookup (Γ , A) zero     =  A
lookup (Γ , B) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥
```

If `lookup Γ n` finds the element in the n-th position, then the
memberhsip proof can be produced algorithmatically. Hence we can
transform a natural number to a membership proof.

```agda
count : (n : ℕ) → Γ ∋ lookup Γ n
count {Γ = Γ , _} zero     =  Z
count {Γ = Γ , _} (suc n)  =  S (count n)
count {Γ = ∅    }  _        =  ⊥-elim impossible
  where postulate impossible : ⊥
```

### Examples 

```agda
_ :  ∅ , A , B ∋ A
_ = count 1

_ : ∅ , B , A ∋ A
_ = count 0
```

Shifting
--------
 
      (Aₙ , ... , A₁, A₀) 
        |    |     |   |
        ↓    ↓     ↓   ↓  
    ↦ (Aₙ , ... , A₁, A₀, B)
  
       n+1         2   1  0

```agda
ext
  : (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

Concatenation
-------------

```agda
_⧺_ : Context → Context → Context
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , x) = Γ ⧺ Δ , x
```

Terms = typing rules
--------------------

First off, since the typing rules for simply typed lambda calculus are
syntax-directed, we combine the term formation rules with the typing
rules.

Therefore, the typing judgement consists of only a context `Γ` and a
`Type` with inference rules as term constructs. The collection of
terms in simply typed lambda calculus is defined as an inducitve family 
indexed by a (given) context and a type. 

```agda
data _⊢_ (Γ : Context) : Type → Set where
```

In our formal development we will use the position of λ to which the
bound variable refer for the name of a variable.  For example,

    λ x. λ y. y

will be represented by

    λ λ 0

This representation is called de Bruijn representation and the nubmer
is a de Bruijn index. It also makes α-equivalence an equality on
λ-terms.

Note that we have

    Γ ∋ (x : A) 
    -----------
    Γ ⊢ x : A

in our informal development where `x` is now merely a number pointing
to the position of `A` in `Γ`. We introduce a term `x` for a free
variable in `Γ` just by giving its position in the context.
Given `Γ ⊢ M : A`, the context Γ is the set of possibly free variables in `M`.

```agda
  `_ : Γ ∋ A
       -----
     → Γ ⊢ A
```
     
The definition of application is straightforward.

```agda
  _·_ : Γ ⊢ A →̇ B
      → Γ ⊢ A
        -----
      → Γ ⊢ B
```

In the informal development it takes a variable x and a term M to
form λ x. M.  Since the name of a variable does not matter at all in
our formal development λ now takes a term M only. 

Moreover, the position of a variable in the context `Γ , A` now refers
to the innermost λ. Hence our definition

```agda
  ƛ_
    : Γ , A ⊢ B
      ---------
    → Γ ⊢ A →̇ B
```

For example, ` Z : (∅ , A) ⊢ A is a variable of type A under the
context (∅ , A).  After abstraction, ƛ ` Z : ∅ ⊢ A →̇ A is an
abstraction under the empty context whose body is only a variable
refering to the variable bound by λ.

As you may have observed, this inductive family Γ ⊢ A is just
a variant of the natural deduction for propositional logic where
inference rules are viewed as term constructs.

For convenience, the following symbols denote a term.

```agda
variable
  M N L M′ N′ L′ : Γ ⊢ A
```
  
Also for convenience, we compute the proof of `Γ ∋ A` by giving its
position n (as a natural). In short, define # n as ` (count n)

```agda
#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
```

### Examples

```agda
nat : Type → Type
nat A = (A →̇ A) →̇ A →̇ A
```

Recall that the Church numberal c₀ for 0 is

    λ f x. x

In the de Bruijn representation, λ f x. x becomes

    λ λ 0

```agda
c₀ : ∀ {A} → ∅ ⊢ nat A
c₀ = ƛ ƛ # 0
```

Similarly, c₁ ≡ λ f x. f x becomes

    λ λ 1 0 

```agda
c₁ : ∀ {A} → ∅ ⊢ nat A
c₁ = ƛ ƛ # 1 · # 0
```

The addition of two Church numerals defined as

    λ n. λ m. λ f. λ x. n f (m f x)

becomes

    λ λ λ λ 3 1 (2 1 0)

```agda
add : ∀ {A} → ∅ ⊢ nat A →̇ nat A →̇ nat A
add = ƛ ƛ ƛ ƛ # 3 · # 1 · (# 2 · # 1 · # 0)
```

### Exercise

Translate the following terms in the informal development to de
Bruijn representation.

    1. (id)   λ x. x
    2. (fst)  λ x y. x
    3. (if)   λ b x y. b x y
    4. (succ) λ n. λ f x. f (n f x)

```agda
id : ∅ ⊢ A →̇ A
id = ƛ ` Z

fst : ∅ ⊢ A →̇ B →̇ A
fst = ƛ ƛ ` (S Z)

bool : Type → Type
bool A = A →̇ A →̇ A

if : ∅ ⊢ bool A →̇ A →̇ A →̇ A
if = ƛ ` Z

succ : ∅ ⊢ nat A →̇ nat A
succ = ƛ ` Z
```

Parallel Substitution
---------------------

To define substitution, it is actually easier to define substitution
for all free variable at once instead of one.

```agda
Rename : Context → Context → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A
```

As the de Bruijn index points to the position of a λ abstraction
starting from the innermost λ, we need to increment/decrement the
number when visiting/leaving λ.

For example, substituting M for x in the following term

    x : A → A ⊢ x (λ y. y) 

becomes

    0 (λ 0) [ M / 0 ] ≡ M (λ [ M ↑ / 1 ])

where M ↑ indicates that the de Bruijn index of a free variable which
is incremented. 

Therefore, a renaming function ρ : ∀ {A} → Γ ∋ A → Δ ∋ A
becomes ext ρ : ∀ {A B} → Γ , B ∋ A → Δ , B ∋ A where B is the type of
argument when visiting an abstraction λ.

```agda
rename : Rename Γ Δ
  → (Γ ⊢ A)
  → (Δ ⊢ A)
rename ρ (` x)   = ` ρ x
rename ρ (M · N) = rename ρ M · rename ρ N
rename ρ (ƛ M)   = ƛ rename (ext ρ) M
```

Similarly, we proceed with a substitution σ : ∀ {A} → Γ ∋ A → Δ ⊢ A.
Note that

    rename S_ : ∀ {A} → Γ ∋ A → Γ , B ∋ A

merely enlarges the context and increments the de Bruijn index for
every Γ ∋ A.

```agda
exts : Subst Γ Δ → Subst (Γ , A) (Δ , A)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ ⊢ A 
  → Subst Γ Δ
  → Δ ⊢ A
(` x)   ⟪ σ ⟫ = σ x
(M · N) ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫
(ƛ M)   ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
```

Singleton Substitution
----------------------

Note that we only need to substitute the free variable corresponding
to the outermost λ, i.e.

    (λ x. M) N -→ M [ N / x ] 

where the free occurrence of x in M points to the outermost λ.
Thus it suffices to define singleton subsitution for the non-empty
context

    Γ , x : A

which appears in the typing rule 

    Γ , x : A ⊢ M : B 
    ----------------------
    Γ ⊢ λ x : A. M : A → B

It follows that the singleton substitution is a special case
of parallel substitution given by

    σN : ∀ {A} → Γ , B ∋ A → Γ ⊢ A 

for some `N : Γ ⊢ B` so that `_⟪ σN ⟫ : Γ , B ⊢ A → Γ ⊢ A`.

```agda
subst-zero : {B : Type}
  → Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z     =  N
subst-zero _ (S x) =  ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
       ---------
     → Γ ⊢ A
_[_] N M =  N ⟪ subst-zero M ⟫
```

Single-step reduction
---------------------

In our informal development -→β is defined only for beta-redex
followed by one-step full β-reduction. These two rules can be combined
altogether.

```agda
infix 3 _-→_
data _-→_ {Γ} : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : (ƛ M) · N -→ M [ N ]

  ξ-ƛ
    :   M -→ M′
    → ƛ M -→ ƛ M′    
  ξ-·ₗ
    :     L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·ᵣ
    :     M -→ M′
      ---------------
    → L · M -→ L · M′
```

Reduction sequence of -→ 
--------------------------------------

The reduction sequence M -↠ N from M to N is just a list of reductions
such that the RHS of a head reduction must be the LHS of the tail of
reductions.

```agda
data _-↠_ {Γ A} : (M N : Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M -↠ M       -- empty list
    
  _-→⟨_⟩_
    : ∀ L          -- this can usually be inferred by the following reduction 
    → L -→ M       -- the head of a list 
    → M -↠ N       -- the tail
      -------
    → L -↠ N

infix  2 _-↠_ 
infixr 2 _-→⟨_⟩_
infix 3 _∎
```

The relation -↠ is also transitive in the sense that

    if L -↠ M and M -↠ N then L -↠ N

the proof itself is in fact the concatenation of two lists.

```agda
_-↠⟨_⟩_ : ∀ L
  → L -↠ M → M -↠ N
  -----------------
  → L -↠ N
M -↠⟨ L-↠M ⟩ M-↠N = {!  !}

infixr 2 _-↠⟨_⟩_
```

### Exercise

Show that -↠ is a congruence. That is, show the following lemmas.

```agda
ƛ-↠ : M -↠ M′
      -----------
    → ƛ M -↠ ƛ M′
ƛ-↠ M-↠M′       = {!!}
  
·-↠ : M -↠ M′
    → N -↠ N′
    → M · N -↠ M′ · N′
·-↠ M-↠M′ N-↠N′ = {!!}
```

Computational equality
----------------------

In (untyped) lambda calculus, we say that two terms M and N are
computationally equal denoted by M =β N if either

    1. M -→ N

    2. M =β M

    3. M =β N
       ------
       N =β M

    4. L =β M    M =β N
       ----------------
           L =β N

Correspondingly, we introduce an inductive type family
where each case is a constrctor of that type family:

```agda
data _=β_ {Γ : Context} : Γ ⊢ A → Γ ⊢ A → Set where
  =β-beta
    : M -→ N → M =β N

  =β-refl
    : M =β M

  =β-sym
    : N =β M → M =β N

  =β-trans
    : L =β M → M =β N
    → L =β N
```

Homework Solution in Agda
-------------------------

Show that if M -↠ N and M is in normal form then M ≡ N (every two
α-equivalent terms are exactly equal in de Bruijn representation).


```
HW2 : M -↠ N → (∀ N → ¬ (M -→ N)) → M ≡ N
HW2 M-↠N M↛ = {!!}
```

Normal form
-----------

Recall that a term M is in normal form if M --̸→ N for any N.  This
property can be characterised completely by its syntax. The
characterisation is given as follows:

    λ x₁ x₂ ⋯ xₙ. x N₁ N₂ ⋯ ⋯ ⋯ Nₘ  
    │             ╰── Neutral ──╯│  
    ╰────────── Normal ──────────╯  

where x is a (free or bound) variable, Nᵢ's are all in normal form,
and n and m can be zero. The syntax is devided into two categories:

  * neutral terms: the neutral part indicates a spine of normal terms
    starting from a variable

  * normal terms: a sequence of abstractions λ followed by neutral
    terms

Neutral terms are those normal terms which do not create any further
β-redexs during substitution. This characterisation is defined as two
mutually-defiend inductive families.

```agda
data Neutral : Γ ⊢ A → Set 
data Normal  : Γ ⊢ A → Set 

data Neutral where
  `_  : (x : Γ ∋ A)
    → Neutral (` x)
  _·_ : Neutral L
    → Normal M
    → Neutral (L · M)

data Normal where
  ᵒ_  : Neutral M → Normal M
  ƛ_  : Normal M  → Normal (ƛ M)
```

The soundness of characterisation is proved by induction on the
derivation of Normal M (resp. Neutral M) and if necessary on M -→ M.

The completeness is proved by induction on the derivation of M
(or Γ ⊢ M : A) and by contradiction using ⊥-elim : ⊥ → A.  so that we
can deduce any property we need once we derive a contradication ⊥.

Proofs are left as exercises. 

### Exercise

```agda
normal-soundness  : Normal M  → ¬ (M -→ N)
neutral-soundness : Neutral M → ¬ (M -→ M′)

normal-soundness  M = {!!}
neutral-soundness M = {!!}

normal-completeness
  : (M : Γ ⊢ A) → (∀ N → ¬ (M -→ N))
  → Normal M 
normal-completeness M = {!!}
```

Preservation
------------

Preservation theorem is trivial in this formal development, since

  M -→ N

is an inductive family indexed by two terms of the same type.

Progress
--------

Progress theorem state that every well-typed term M is either

  1. in normal form or
  2. reducible

so we introduce a predicate `Progress` over well-typed terms M for
this statement.

```agda
data Progress (M : Γ ⊢ A) : Set where
  step
    : M -→ N
      ----------
    → Progress M

  done : Normal M
    → Progress M
```

Progress theorm is proved by induction on the derviation of Γ ⊢ M : A
in the informal and formal developments.

```agda
progress : (M : Γ ⊢ A)
  → Progress M
progress M = {!!}
```

Progress Theorem can be proved without `Normal`. Then, why bother?
Despite of being logically equivalent, the proof becomes really ugly!
Try the following exericse at your own risk.

```agda
data Progress′ (M : Γ ⊢ A) : Set where
  step
    : (r : M -→ N)
      ----------
    → Progress′ M

  done : (M↓ : (N : Γ ⊢ A) → M -→ N → ⊥)
    → Progress′ M

progress′ : (M : Γ ⊢ A) → Progress′ M
progress′ M = {!!}
```