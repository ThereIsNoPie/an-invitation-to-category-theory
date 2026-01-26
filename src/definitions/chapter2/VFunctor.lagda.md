---
layout: agda
title: "V-Functor (Enriched Functor)"
section: "Definitions"
chapter: 2
number: 48
---

# V-Functor (Enriched Functor)

## Textbook Definition

**Definition 2.47.** Let $\mathcal{X}$ and $\mathcal{Y}$ be $\mathcal{V}$-categories. A *$\mathcal{V}$-functor from $\mathcal{X}$ to $\mathcal{Y}$*, denoted $F : \mathcal{X} \to \mathcal{Y}$, consists of one constituent:

(i) a function $F : \text{Ob}(\mathcal{X}) \to \text{Ob}(\mathcal{Y})$

subject to one constraint:

(a) for all $x_1, x_2 \in \text{Ob}(\mathcal{X})$, one has $\mathcal{X}(x_1, x_2) \leq \mathcal{Y}(F(x_1), F(x_2))$.

## Agda Setup

```agda
module definitions.chapter2.VFunctor where

open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import definitions.chapter2.VCategory using (VCategory)
open import Data.Product using (Σ; Σ-syntax; _,_)
```

## Agda Formalization

```agda
record IsVFunctor
  {V : SymmetricMonoidalPreorder}
  (X Y : VCategory V)
  (F : VCategory.Ob X → VCategory.Ob Y)
  : Set where

  private
    module X = VCategory X
    module Y = VCategory Y

  open SymmetricMonoidalPreorder V using (_≤_)

  field
    -- (a) X(x₁, x₂) ≤ Y(F(x₁), F(x₂))
    preserves-hom : ∀ {x₁ x₂ : X.Ob} → X.hom x₁ x₂ ≤ Y.hom (F x₁) (F x₂)

-- A V-functor: function on objects + proof of the constraint
VFunctor : {V : SymmetricMonoidalPreorder} → VCategory V → VCategory V → Set
VFunctor {V} X Y = Σ[ F ∈ (VCategory.Ob X → VCategory.Ob Y) ] (IsVFunctor X Y F)
```

## Identity and Composition

```agda
-- Identity V-functor
id-VFunctor : {V : SymmetricMonoidalPreorder} {X : VCategory V} → VFunctor X X
id-VFunctor {V} = (λ x → x) , record { preserves-hom = reflexive }
  where open SymmetricMonoidalPreorder V

-- Composition of V-functors
_∘V_ : {V : SymmetricMonoidalPreorder} {X Y Z : VCategory V}
     → VFunctor Y Z → VFunctor X Y → VFunctor X Z
_∘V_ {V} (G , G-is) (F , F-is) = (λ x → G (F x)) , record
  { preserves-hom = transitive F-pres G-pres
  }
  where
    open SymmetricMonoidalPreorder V
    F-pres = IsVFunctor.preserves-hom F-is
    G-pres = IsVFunctor.preserves-hom G-is
```

## Interpretation

The condition $\mathcal{X}(x_1, x_2) \leq \mathcal{Y}(F(x_1), F(x_2))$ says that the "cost" to get from $x_1$ to $x_2$ in $\mathcal{X}$ is at least as much as the cost to get from $F(x_1)$ to $F(x_2)$ in $\mathcal{Y}$.

In other words, $F$ can only make things "easier", never harder.
