---
layout: agda
title: "Reals as Metric Space"
section: "Examples"
chapter: 2
number: 37
---

# Reals as Metric Space

## Textbook Description

**Example 2.37.** The set ℝ of real numbers can be given a metric space structure, and hence a Lawvere metric space structure. Namely d(x, y) := |y - x|, the absolute value of the difference. So d(3, 7) = 4.

## Agda Setup

```agda
module examples.chapter2.RealsAsMetricSpace where

open import definitions.chapter2.LawvereMetricSpace using (LawvereMetricSpace)
open import definitions.chapter2.VCategory using (VCategory)
open import examples.chapter2.Cost using (Cost; [0,∞]; _≥_; _+ℝ_; 0ℝ; ≥-refl; ≥-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## The Example

We construct ℝ as a Lawvere metric space with distance d(x, y) = |y - x|.

```agda
-- We postulate the real numbers and their properties
postulate
  ℝ : Set

  -- The distance function: absolute value of difference
  abs-diff : ℝ → ℝ → [0,∞]

  -- d(x, x) = 0 (reflexivity)
  abs-diff-zero : ∀ {x : ℝ} → abs-diff x x ≡ 0ℝ

  -- 0 ≥ d(x, x) follows from d(x, x) = 0
  abs-diff-identity : ∀ {x : ℝ} → 0ℝ ≥ abs-diff x x

  -- Triangle inequality: |x - y| + |y - z| ≥ |x - z|
  abs-diff-triangle : ∀ {x y z : ℝ} → (abs-diff x y +ℝ abs-diff y z) ≥ abs-diff x z

-- The reals form a Lawvere metric space
ℝ-metric : LawvereMetricSpace
```

### Implementation

**Strategy:** We construct a Cost-category with ℝ as objects and |y - x| as the hom-object (distance).

```agda
ℝ-metric = record
  { Ob = ℝ
  ; hom = abs-diff
  ; identity = abs-diff-identity
  ; composition = abs-diff-triangle
  }
```

## Symmetry

Unlike general Lawvere metric spaces, the standard metric on ℝ is symmetric: d(x, y) = d(y, x).

```agda
postulate
  -- The standard metric is symmetric: |x - y| = |y - x|
  abs-diff-sym : ∀ {x y : ℝ} → abs-diff x y ≡ abs-diff y x
```

## Interpretation

The real numbers with the standard distance function form a **symmetric** Lawvere metric space. This is a special case where:

1. **Symmetry holds**: |x - y| = |y - x| for all x, y
2. **Separation holds**: if |x - y| = 0 then x = y
3. **Distances are finite**: |x - y| < ∞ for all x, y ∈ ℝ

This example shows that ordinary metric spaces embed naturally into the more general framework of Lawvere metric spaces (Cost-categories).
```
