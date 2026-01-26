---
layout: agda
title: "Opposite, Dagger, and Skeletal V-Categories"
section: "Exercises"
chapter: 2
number: 52
---

# Opposite, Dagger, and Skeletal V-Categories

## Textbook Description

**Exercise 2.50.** The concepts of opposite, dagger, and skeleton extend from preorders to V-categories.

The *opposite* of a V-category $\mathcal{X}$ is denoted $\mathcal{X}^{\text{op}}$ and is defined by:
- $\text{Ob}(\mathcal{X}^{\text{op}}) := \text{Ob}(\mathcal{X})$
- For all $x, y \in \mathcal{X}$, we have $\mathcal{X}^{\text{op}}(x, y) := \mathcal{X}(y, x)$

A V-category $\mathcal{X}$ is a *dagger* V-category if the identity function is a V-functor $\dagger : \mathcal{X} \to \mathcal{X}^{\text{op}}$.

A *skeletal* V-category is one in which if $I \leq \mathcal{X}(x, y)$ and $I \leq \mathcal{X}(y, x)$, then $x = y$.

1. Show that a skeletal dagger Cost-category is an extended metric space.
2. Use this to make sense of the analogy: "preorders are to sets as Lawvere metric spaces are to extended metric spaces."

## Agda Setup

```agda
module exercises.chapter2.OppositeDaggerSkeletal where

open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import definitions.chapter2.VCategory using (VCategory)
open import definitions.chapter2.VFunctor using (VFunctor; IsVFunctor)
open import definitions.chapter2.LawvereMetricSpace using (LawvereMetricSpace)
open import examples.chapter2.Cost using (Cost; [0,∞]; 0∞; _≥_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
```

## Opposite V-Category

```agda
-- The opposite of a V-category reverses the hom-objects
op : {V : SymmetricMonoidalPreorder} → VCategory V → VCategory V
op {V} X = record
  { Ob = Ob
  ; hom = λ x y → hom y x   -- reversed!
  ; identity = identity
  ; composition = λ {x} {y} {z} →
      -- Need: hom(y,x) ⊗ hom(z,y) ≤ hom(z,x)
      -- From X with a=z, b=y, c=x: hom(z,y) ⊗ hom(y,x) ≤ hom(z,x)
      -- Use symmetry: hom(y,x) ⊗ hom(z,y) = hom(z,y) ⊗ hom(y,x)
      subst (_≤ hom z x) symmetry composition
  }
  where
    open VCategory X
    open SymmetricMonoidalPreorder V
```

## Dagger V-Category

A V-category is dagger if the identity function is a V-functor to the opposite.

```agda
-- The dagger condition: X(x,y) ≤ X(y,x) for all x, y
-- This means the identity function id : X → X^op is a V-functor
IsDagger : {V : SymmetricMonoidalPreorder} → VCategory V → Set
IsDagger {V} X = ∀ {x y} → hom x y ≤ hom y x
  where
    open VCategory X
    open SymmetricMonoidalPreorder V
```

## Skeletal V-Category

A V-category is skeletal if whenever I ≤ X(x,y) and I ≤ X(y,x), we have x = y.

```agda
-- The skeletal condition: I ≤ X(x,y) and I ≤ X(y,x) implies x = y
IsSkeletal : {V : SymmetricMonoidalPreorder} → VCategory V → Set
IsSkeletal {V} X = ∀ {x y} → I ≤ hom x y → I ≤ hom y x → x ≡ y
  where
    open VCategory X
    open SymmetricMonoidalPreorder V
```

## Skeletal Dagger Cost-Categories are Extended Metric Spaces

For Cost-categories (Lawvere metric spaces):
- Dagger means d(x,y) ≥ d(y,x), i.e., the metric is symmetric
- Skeletal means 0 ≥ d(x,y) and 0 ≥ d(y,x) implies x = y

Together with the Lawvere metric space axioms, this gives an extended metric space.

```agda
-- A skeletal dagger Cost-category satisfies:
-- 1. d(x,x) = 0           (from identity: 0 ≥ d(x,x), and d ≥ 0)
-- 2. d(x,z) ≤ d(x,y) + d(y,z)  (triangle inequality from composition)
-- 3. d(x,y) = d(y,x)      (symmetry from dagger)
-- 4. d(x,y) = 0 → x = y   (from skeletal: 0 ≥ d(x,y) means d(x,y) = 0)

-- This is exactly the definition of an extended metric space!
-- (Extended because d(x,y) can be ∞)

record IsExtendedMetricSpace (X : LawvereMetricSpace) : Set where
  open VCategory X

  field
    symmetric : ∀ {x y} → hom x y ≡ hom y x
    separates : ∀ {x y} → hom x y ≡ 0∞ → x ≡ y

-- From dagger + skeletal, we get an extended metric space
postulate
  skeletal-dagger→extended :
    (X : LawvereMetricSpace) →
    IsDagger X →
    IsSkeletal X →
    IsExtendedMetricSpace X
```

## The Analogy

The exercise asks us to make sense of:

> "Preorders are to sets as Lawvere metric spaces are to extended metric spaces."

```agda
{-
The analogy works as follows:

| Preorder concept | Lawvere metric space concept |
|------------------|------------------------------|
| Preorder         | Lawvere metric space         |
| Skeletal preorder (partial order) | Skeletal Cost-category |
| Dagger preorder (equivalence relation) | Dagger Cost-category (symmetric) |
| Skeletal + Dagger = Discrete preorder | Skeletal + Dagger = Extended metric space |
| Discrete preorder ≅ Set | Extended metric space has d(x,y) = 0 ↔ x = y |

A discrete preorder is one where x ≤ y implies x = y.
This "forgets" all the structure, leaving just a set.

An extended metric space is one where d(x,y) = 0 implies x = y.
This "forgets" the asymmetry and non-separation, leaving just distances.

So: preorders can be "quotiented" to sets (via skeletal + dagger)
    Lawvere metric spaces can be "quotiented" to extended metric spaces (via skeletal + dagger)
-}
```
