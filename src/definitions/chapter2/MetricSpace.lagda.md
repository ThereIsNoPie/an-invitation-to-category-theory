---
layout: agda
title: "Metric Space"
section: "Definitions"
chapter: 2
number: 34
---

# Metric Space

## Textbook Definition

**Definition 2.34.** A *metric space* (X, d) consists of:

(i) a set X, elements of which are called *points*, and

(ii) a function d : X × X → ℝ≥0, where d(x, y) is called the *distance between x and y*.

These constituents must satisfy four properties:

(a) for every x ∈ X, we have d(x, x) = 0,

(b) for every x, y ∈ X, if d(x, y) = 0 then x = y,

(c) for every x, y ∈ X, we have d(x, y) = d(y, x), and

(d) for every x, y, z ∈ X, we have d(x, y) + d(y, z) ≥ d(x, z).

The fourth property is called the *triangle inequality*.

If we ask instead in (ii) for a function d : X × X → [0, ∞] = ℝ≥0 ∪ {∞}, we call (X, d) an *extended* metric space.

## Agda Setup

```agda
module definitions.chapter2.MetricSpace where

open import plumbing.Reals using ([0,∞]; 0∞; _+ℝ_; _≥_)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## Agda Formalization

We use [0,∞] from plumbing.Reals for distances. This covers both ordinary metric spaces (where distances happen to be finite) and extended metric spaces (where ∞ is allowed).

```agda
-- A metric space (X, d) with the four axioms
record MetricSpace : Set₁ where
  field
    -- (i) A set of points
    X : Set

    -- (ii) A distance function
    d : X → X → [0,∞]

    -- (a) Zero self-distance: d(x, x) = 0
    zero-self : ∀ {x : X} → d x x ≡ 0∞

    -- (b) Separation (identity of indiscernibles): d(x, y) = 0 implies x = y
    separation : ∀ {x y : X} → d x y ≡ 0∞ → x ≡ y

    -- (c) Symmetry: d(x, y) = d(y, x)
    symmetry : ∀ {x y : X} → d x y ≡ d y x

    -- (d) Triangle inequality: d(x, y) + d(y, z) ≥ d(x, z)
    triangle : ∀ {x y z : X} → (d x y +ℝ d y z) ≥ d x z
```

## Comparison with Lawvere Metric Spaces

Lawvere metric spaces (Definition 2.36) relax the ordinary metric space axioms:

| Property | Ordinary Metric Space | Lawvere Metric Space |
|----------|----------------------|---------------------|
| Zero self-distance | d(x,x) = 0 | d(x,x) = 0 |
| Separation | d(x,y) = 0 → x = y | Not required |
| Symmetry | d(x,y) = d(y,x) | Not required |
| Triangle inequality | d(x,y) + d(y,z) ≥ d(x,z) | d(x,y) + d(y,z) ≥ d(x,z) |

The textbook explains why dropping separation and symmetry is useful:
- **Asymmetric distances**: effort to go uphill ≠ effort to go downhill
- **Non-separating distances**: distance from Boston to US is 0, but Boston ≠ US
```
