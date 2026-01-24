---
layout: agda
title: "Lawvere Metric Space"
section: "Definitions"
chapter: 2
number: 36
---

# Lawvere Metric Space

## Textbook Definition

**Definition 2.36.** A *Lawvere metric space* is a Cost-category.

This is a very compact definition, but it packs a punch. Let's work out what it means, by relating it to the usual definition of metric space. By Definition 2.30, a Cost-category X consists of:

(i) a set Ob(X),

(ii) for every x, y ∈ Ob(X) an element X(x, y) ∈ [0, ∞].

Here the set Ob(X) is playing the role of the set of points, and X(x, y) ∈ [0, ∞] is playing the role of distance, so let's write a little translator:

X := Ob(X)    d(x, y) := X(x, y)

The properties of a category enriched in Cost are:

(a) 0 ≥ d(x, x) for all x ∈ X, and

(b) d(x, y) + d(y, z) ≥ d(x, z) for all x, y, z ∈ X.

Since d(x, x) ∈ [0, ∞], if 0 ≥ d(x, x) then d(x, x) = 0. So the first condition is equivalent to the first condition from the ordinary metric space definition, namely d(x, x) = 0. The second condition is the triangle inequality.

## Agda Setup

```agda
module definitions.chapter2.LawvereMetricSpace where

open import definitions.chapter2.VCategory using (VCategory)
open import examples.chapter2.Cost using (Cost; [0,∞]; _≥_; _+ℝ_; 0ℝ; ∞)
```

## Agda Formalization

A Lawvere metric space is simply a V-category enriched in Cost.

```agda
-- A Lawvere metric space is a Cost-category
LawvereMetricSpace : Set₁
LawvereMetricSpace = VCategory Cost
```

## Unpacking the Definition

For convenience, we provide accessor functions that use metric space terminology.

```agda
module LawvereMetricSpaceOps (X : LawvereMetricSpace) where
  open VCategory X public

  -- The set of points
  Point : Set
  Point = Ob

  -- The distance function d(x, y)
  d : Point → Point → [0,∞]
  d = hom

  -- Property (a): d(x, x) = 0
  -- From identity: 0ℝ ≥ d(x, x), and since d(x,x) ∈ [0,∞], this means d(x,x) = 0
  zero-self-distance : ∀ {x : Point} → 0ℝ ≥ d x x
  zero-self-distance = identity

  -- Property (b): Triangle inequality
  -- d(x, y) + d(y, z) ≥ d(x, z)
  triangle-inequality : ∀ {x y z : Point} → (d x y +ℝ d y z) ≥ d x z
  triangle-inequality = composition
```

## Interpretation

Lawvere metric spaces generalize ordinary metric spaces by:

1. **Dropping symmetry**: d(x, y) need not equal d(y, x). This allows modeling directed distances like "effort to go uphill" vs "effort to go downhill".

2. **Dropping separation**: d(x, y) = 0 does not imply x = y. This allows modeling regions where "the distance from Boston to the US is 0" but they are not equal.

3. **Allowing infinity**: d(x, y) can be ∞, modeling unreachable points.

The key insight is that the axioms of a V-category enriched in Cost precisely capture the essential properties of distance: zero self-distance (reflexivity) and the triangle inequality (transitivity of "getting there").
```
