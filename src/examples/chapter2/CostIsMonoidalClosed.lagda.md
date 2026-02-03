---
layout: agda
title: "Cost is Monoidal Closed"
section: "Examples"
chapter: 2
number: 60
---

# Cost is Monoidal Closed

## Textbook Description

**Example 2.57.** The monoidal preorder $\text{Cost} = ([0, \infty], \geq, 0, +)$ is monoidal closed. Indeed, for any $x, y \in [0, \infty]$, define $x \multimap y := \max(0, y - x)$. Then, for any $a, x, y \in [0, \infty]$, we have:

$$a + x \geq y \quad \text{iff} \quad a \geq y - x \quad \text{iff} \quad \max(0, a) \geq \max(0, y - x) \quad \text{iff} \quad a \geq (x \multimap y)$$

Note that we have not considered subtraction in Cost before; we can in fact use monoidal closure to *define* subtraction in terms of the order and monoidal structure!

## Agda Setup

```agda
module examples.chapter2.CostIsMonoidalClosed where

open import definitions.chapter2.MonoidalClosed
  using (IsMonoidalClosed; MonoidalClosedPreorder)
open import examples.chapter2.Cost using (Cost; [0,∞]; 0∞; ∞; _≥_; _+ℝ_)
open import Data.Product using (_,_)
```

## The Hom-Element

In Cost, the hom-element (internal hom) is truncated subtraction:

$x \multimap y = \max(0, y - x)$

```agda
postulate
  -- Truncated subtraction: max(0, y - x)
  _⊸_ : [0,∞] → [0,∞] → [0,∞]

  -- The closure property: (a + x) ≥ y iff a ≥ max(0, y - x)
  Cost-curry : ∀ {a x y : [0,∞]} → (a +ℝ x) ≥ y → a ≥ (x ⊸ y)
  Cost-uncurry : ∀ {a x y : [0,∞]} → a ≥ (x ⊸ y) → (a +ℝ x) ≥ y
```

## Cost as Monoidal Closed

```agda
Cost-closed : IsMonoidalClosed Cost
Cost-closed = record
  { _⊸_ = _⊸_
  ; curry = Cost-curry
  ; uncurry = Cost-uncurry
  }

Cost-MCP : MonoidalClosedPreorder
Cost-MCP = record
  { base = Cost
  ; closed = Cost-closed
  }
```

## Interpretation

The hom-element $x \multimap y = \max(0, y - x)$ represents "the additional cost needed to go from having $x$ resources to having $y$ resources."

- If $y \leq x$: we already have enough, so the extra cost is 0
- If $y > x$: we need $(y - x)$ more

This is why the adjunction $(a + x) \geq y \Leftrightarrow a \geq (x \multimap y)$ makes sense: the total resources $a + x$ are at least $y$ if and only if the additional resources $a$ cover the shortfall $\max(0, y - x)$.
