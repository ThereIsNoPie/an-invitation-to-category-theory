---
layout: agda
title: "Cost is Monoidal Closed"
section: "Examples"
chapter: 2
number: 60
---

# Cost is Monoidal Closed

## Textbook Description

**Example 2.60.** The monoidal preorder $\text{Cost} = ([0, \infty], \geq, 0, +)$ is monoidal closed. Indeed, for any $x, y \in [0, \infty]$, define $x \multimap y := \max(0, y - x)$. Then, for any $a, x, y \in [0, \infty]$, we have:

$$a + x \geq y \quad \text{iff} \quad a \geq y - x \quad \text{iff} \quad \max(0, a) \geq \max(0, y - x) \quad \text{iff} \quad a \geq (x \multimap y)$$

Note that we have not considered subtraction in Cost before; we can in fact use monoidal closure to *define* subtraction in terms of the order and monoidal structure!

## Agda Setup

```agda
module examples.chapter2.CostIsMonoidalClosed where

open import definitions.chapter2.MonoidalClosed
  using (IsMonoidalClosed; MonoidalClosedPreorder)
open import examples.chapter2.Cost using (Cost; [0,∞]; _≥_; _+ℝ_)
open import plumbing.Reals using (_∸_; ∸-adjunctˡ; ∸-adjunctʳ)
open import Data.Product using (_,_)
```

## The Hom-Element

In Cost the hom-element is **truncated subtraction** (monus): $x \multimap y = \max(0, y - x)$, which the plumbing provides as $y \mathbin{∸} x$.

```agda
-- x ⊸ y = max(0, y - x), i.e. monus with the arguments swapped
_⊸_ : [0,∞] → [0,∞] → [0,∞]
x ⊸ y = y ∸ x
```

The claim is that this makes Cost monoidal closed:

```agda
Cost-closed : IsMonoidalClosed Cost

Cost-MCP : MonoidalClosedPreorder
```

## Construction

The closure condition unfolds, in Cost's reversed order, to exactly the
adjunction that *defines* truncated subtraction:

- `curry`:   $(a + x) \geq y \;\to\; a \geq (x \multimap y)$, i.e. $(a + x) \geq y \to a \geq (y ∸ x)$
- `uncurry`: $a \geq (x \multimap y) \;\to\; (a + x) \geq y$

So both directions are immediate from the monus adjunction in `plumbing.Reals` —
no calculation beyond unfolding `x ⊸ y = y ∸ x`.

```agda
Cost-closed = record
  { _⊸_ = _⊸_
  ; curry = ∸-adjunctˡ
  ; uncurry = ∸-adjunctʳ
  }

Cost-MCP = record
  { base = Cost
  ; closed = Cost-closed
  }
```

## Interpretation

The hom-element $x \multimap y = \max(0, y - x)$ is "the additional cost needed to upgrade from $x$ resources to $y$ resources."

- If $y \leq x$: we already have enough, so the extra cost is $0$.
- If $y \gt x$: we need $(y - x)$ more.

The adjunction $(a + x) \geq y \Leftrightarrow a \geq (x \multimap y)$ then reads: a budget of $a$ on top of $x$ covers $y$ exactly when $a$ alone covers the shortfall $\max(0, y - x)$.

The striking part is the direction of definition. Cost's monoid gives only **addition** — there is no subtraction in the structure. But because Cost is *closed*, the hom-element *is* a subtraction operation, built purely from the order ($\geq$) and addition ($+$). This is the "internalization" idea made concrete: closure lets the preorder express an operation that was not in its original vocabulary.
