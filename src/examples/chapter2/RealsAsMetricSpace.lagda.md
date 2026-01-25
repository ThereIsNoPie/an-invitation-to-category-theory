---
layout: agda
title: "Reals as Metric Space"
section: "Examples"
chapter: 2
number: 37
---

# Reals as Metric Space

## Textbook Description

**Example 2.37.** The set $\mathbb{R}$ of real numbers can be given a metric space structure, and hence a Lawvere metric space structure. Namely $d(x, y) := \lvert y - x \rvert$, the absolute value of the difference. So $d(3, 7) = 4$.

## Agda Setup

```agda
module examples.chapter2.RealsAsMetricSpace where

open import plumbing.Reals using (ℝ; [0,∞]; 0∞; _≥_; _+ℝ_; dist; dist-refl; dist-triangle; dist-sym; 0-least)
open import definitions.chapter2.LawvereMetricSpace using (LawvereMetricSpace)
open import definitions.chapter2.VCategory using (VCategory)
open import examples.chapter2.Cost using (Cost)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
```

## The Example

We construct $\mathbb{R}$ as a Lawvere metric space with distance $d(x, y) = \lvert y - x \rvert$.

```agda
-- We need: 0 ≥ dist x x, which follows from dist x x = 0∞ and x ≥ 0∞ for all x
0≥dist-refl : ∀ {x : ℝ} → 0∞ ≥ dist x x
0≥dist-refl {x} = subst (0∞ ≥_) (sym dist-refl) 0-least

-- The reals form a Lawvere metric space
ℝ-metric : LawvereMetricSpace
```

### Implementation

**Strategy:** We construct a Cost-category with $\mathbb{R}$ as objects and dist as the hom-object.

```agda
ℝ-metric = record
  { Ob = ℝ
  ; hom = dist
  ; identity = 0≥dist-refl
  ; composition = dist-triangle
  }
```

## Interpretation

The real numbers with the standard distance function form a **symmetric** Lawvere metric space. This is a special case where:

1. **Symmetry holds**: $d(x, y) = d(y, x)$ for all $x, y$ (from dist-sym)
2. **Separation holds**: if $d(x, y) = 0$ then $x = y$
3. **Distances are finite**: $d(x, y) < \infty$ for all $x, y \in \mathbb{R}$

This example shows that ordinary metric spaces embed naturally into the more general framework of Lawvere metric spaces (Cost-categories).
