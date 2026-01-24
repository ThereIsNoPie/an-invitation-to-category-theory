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

open import Relation.Binary.PropositionalEquality using (_≡_)
```

## Agda Formalization

We postulate nonnegative reals and define metric spaces as a record.

```agda
-- Postulate the nonnegative reals
postulate
  ℝ≥0 : Set
  0ℝ : ℝ≥0
  _+ℝ_ : ℝ≥0 → ℝ≥0 → ℝ≥0
  _≥ℝ_ : ℝ≥0 → ℝ≥0 → Set

-- A metric space (X, d) with the four axioms
record MetricSpace : Set₁ where
  field
    -- (i) A set of points
    X : Set

    -- (ii) A distance function
    d : X → X → ℝ≥0

    -- (a) Zero self-distance: d(x, x) = 0
    zero-self : ∀ {x : X} → d x x ≡ 0ℝ

    -- (b) Separation (identity of indiscernibles): d(x, y) = 0 implies x = y
    separation : ∀ {x y : X} → d x y ≡ 0ℝ → x ≡ y

    -- (c) Symmetry: d(x, y) = d(y, x)
    symmetry : ∀ {x y : X} → d x y ≡ d y x

    -- (d) Triangle inequality: d(x, y) + d(y, z) ≥ d(x, z)
    triangle : ∀ {x y z : X} → (d x y +ℝ d y z) ≥ℝ d x z
```

## Extended Metric Space

For extended metric spaces, we allow distances to be infinite.

```agda
-- Postulate extended nonnegative reals [0, ∞]
postulate
  [0,∞] : Set
  0∞ : [0,∞]
  ∞ : [0,∞]
  _+∞_ : [0,∞] → [0,∞] → [0,∞]
  _≥∞_ : [0,∞] → [0,∞] → Set

-- An extended metric space allows infinite distances
record ExtendedMetricSpace : Set₁ where
  field
    -- (i) A set of points
    X : Set

    -- (ii) A distance function (now to [0, ∞])
    d : X → X → [0,∞]

    -- (a) Zero self-distance
    zero-self : ∀ {x : X} → d x x ≡ 0∞

    -- (b) Separation
    separation : ∀ {x y : X} → d x y ≡ 0∞ → x ≡ y

    -- (c) Symmetry
    symmetry : ∀ {x y : X} → d x y ≡ d y x

    -- (d) Triangle inequality
    triangle : ∀ {x y z : X} → (d x y +∞ d y z) ≥∞ d x z
```

## Comparison with Lawvere Metric Spaces

Lawvere metric spaces (Definition 2.36) relax the ordinary metric space axioms:

| Property | Ordinary Metric Space | Lawvere Metric Space |
|----------|----------------------|---------------------|
| Zero self-distance | d(x,x) = 0 | d(x,x) = 0 |
| Separation | d(x,y) = 0 → x = y | Not required |
| Symmetry | d(x,y) = d(y,x) | Not required |
| Triangle inequality | d(x,y) + d(y,z) ≥ d(x,z) | d(x,y) + d(y,z) ≥ d(x,z) |
| Infinite distances | Only in extended version | Always allowed |

The textbook explains why dropping separation and symmetry is useful:
- **Asymmetric distances**: effort to go uphill ≠ effort to go downhill
- **Non-separating distances**: distance from Boston to US is 0, but Boston ≠ US
```
