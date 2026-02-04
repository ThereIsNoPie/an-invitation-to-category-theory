---
layout: agda
title: "Opposite, Dagger, and Skeletal V-Categories"
section: "Exercises"
chapter: 2
number: 52
---

# Opposite, Dagger, and Skeletal V-Categories

## Textbook Description

**Exercise 2.52.** The concepts of opposite, dagger, and skeleton extend from preorders to V-categories.

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
open import definitions.chapter2.MetricSpace using (MetricSpace)
open import examples.chapter2.Cost using (Cost; [0,∞]; 0∞; _≥_; ≥-refl; ≥-antisym; 0-least)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
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

## Problem

A skeletal dagger Cost-category satisfies all four metric space axioms (Definition 2.34):
1. d(x,x) = 0 — from identity: 0 ≥ d(x,x), and d ≥ 0
2. d(x,y) = 0 → x = y — from skeletal
3. d(x,y) = d(y,x) — symmetry from dagger
4. d(x,y) + d(y,z) ≥ d(x,z) — triangle inequality from composition

Show that a skeletal dagger Cost-category is an extended metric space.

```agda
skeletal-dagger→metric :
  (X : LawvereMetricSpace) →
  IsDagger X →
  IsSkeletal X →
  MetricSpace
```

## Solution

**Strategy:** A Lawvere metric space already provides zero self-distance and the triangle inequality. Dagger adds symmetry, and skeletal adds separation.

- **zero-self**: identity gives `0 ≥ d(x,x)`, and `0-least` gives `d(x,x) ≥ 0`. Apply `≥-antisym`.
- **symmetry**: dagger in both directions gives `d(x,y) ≥ d(y,x)` and `d(y,x) ≥ d(x,y)`. Apply `≥-antisym`.
- **separation**: given `d(x,y) ≡ 0`, use dagger to get `0 ≥ d(y,x)`, combine with `0-least` and `≥-antisym` to get `d(y,x) ≡ 0`. Then both directions are zero, so skeletal gives `x ≡ y`.
- **triangle**: directly from composition.

```agda
skeletal-dagger→metric X dagger skeletal = record
  { X = Ob
  ; d = hom
  ; zero-self = ≥-antisym 0-least identity
  ; symmetry = λ {x} {y} →
      ≥-antisym (dagger {x} {y}) (dagger {y} {x})
  ; separation = λ {x} {y} hxy≡0 →
      let 0≥hyx = subst (_≥ hom y x) hxy≡0 (dagger {x} {y})
          hyx≡0 = ≥-antisym 0-least 0≥hyx
      in skeletal (subst (0∞ ≥_) (sym hxy≡0) ≥-refl)
                  (subst (0∞ ≥_) (sym hyx≡0) ≥-refl)
  ; triangle = composition
  }
  where open VCategory X
```

## The Analogy

The exercise asks us to make sense of:

> "Preorders are to sets as Lawvere metric spaces are to extended metric spaces."

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

So: preorders can be "quotiented" to sets (via skeletal + dagger),
and Lawvere metric spaces can be "quotiented" to extended metric spaces (via skeletal + dagger).
