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

open import plumbing.Reals using (ℝ; [0,∞]; 0∞; dist; dist-refl; dist-triangle; dist-sym; dist-zero→eq)
open import definitions.chapter2.MetricSpace using (MetricSpace)
open import definitions.chapter2.LawvereMetricSpace using (LawvereMetricSpace; fromMetricSpace)
```

## The Real Numbers as a Metric Space

We first construct $\mathbb{R}$ as an ordinary metric space with distance $d(x, y) = \lvert y - x \rvert$.

```agda
ℝ-MetricSpace : MetricSpace
ℝ-MetricSpace = record
  { X = ℝ
  ; d = dist
  ; zero-self = dist-refl
  ; separation = dist-zero→eq
  ; symmetry = dist-sym
  ; triangle = dist-triangle
  }
```

## The Real Numbers as a Lawvere Metric Space

Every metric space gives rise to a Lawvere metric space. We simply apply the conversion.

```agda
ℝ-LawvereMetricSpace : LawvereMetricSpace
ℝ-LawvereMetricSpace = fromMetricSpace ℝ-MetricSpace
```

## Interpretation

The real numbers with the standard distance function form a **symmetric** Lawvere metric space. This is a special case where:

1. **Symmetry holds**: $d(x, y) = d(y, x)$ for all $x, y$ (from dist-sym)
2. **Separation holds**: if $d(x, y) = 0$ then $x = y$
3. **Distances are finite**: $d(x, y) < \infty$ for all $x, y \in \mathbb{R}$

This example shows that ordinary metric spaces embed naturally into the more general framework of Lawvere metric spaces (Cost-categories).
