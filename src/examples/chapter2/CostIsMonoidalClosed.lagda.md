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

Both cases on the number line — the blue segment is the hom-element (the
shortfall), and the dashed arrow is a budget $a$ added on top of $x$; it reaches
$y$ exactly when $a$ is at least the shortfall:

```svg
<svg viewBox="0 0 500 260" role="img" aria-label="Two number lines. Top: y greater than x, the gap from x to y is the shortfall x ⊸ y = y − x, and a dashed budget arrow from x reaches past y exactly when a is at least the shortfall. Bottom: y at most x, the shortfall is zero, nothing to add">
  <path d="M 180 46 L 394 46" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" fill="none" marker-end="url(#arrow)"/>
  <text x="290" y="36" font-size="14" text-anchor="middle" fill="var(--agda-type)">+ a</text>
  <line x1="180" y1="66" x2="180" y2="78" stroke="var(--agda-function)" stroke-width="2"/>
  <line x1="340" y1="66" x2="340" y2="78" stroke="var(--agda-function)" stroke-width="2"/>
  <line x1="180" y1="72" x2="340" y2="72" stroke="var(--agda-function)" stroke-width="2"/>
  <text x="260" y="62" font-size="14" text-anchor="middle" fill="var(--agda-function)">x ⊸ y = y − x</text>
  <line x1="25" y1="100" x2="475" y2="100" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="40" y1="94" x2="40" y2="106" stroke="currentColor" opacity="0.5"/>
  <line x1="400" y1="52" x2="400" y2="94" stroke="currentColor" opacity="0.35" stroke-dasharray="2 3"/>
  <circle cx="180" cy="100" r="4.5" fill="currentColor"/>
  <circle cx="340" cy="100" r="4.5" fill="currentColor"/>
  <circle cx="400" cy="100" r="4.5" fill="none" stroke="currentColor" stroke-width="1.5"/>
  <text x="40" y="126" font-size="14" text-anchor="middle" fill="currentColor">0</text>
  <text x="180" y="126" font-size="16" text-anchor="middle" fill="currentColor">x</text>
  <text x="340" y="126" font-size="16" text-anchor="middle" fill="currentColor">y</text>
  <text x="400" y="126" font-size="14" text-anchor="middle" fill="currentColor" opacity="0.7">x + a</text>
  <text x="250" y="182" font-size="14" text-anchor="middle" fill="var(--agda-function)">x ⊸ y = 0 — already at y or beyond</text>
  <line x1="25" y1="210" x2="475" y2="210" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="40" y1="204" x2="40" y2="216" stroke="currentColor" opacity="0.5"/>
  <circle cx="160" cy="210" r="4.5" fill="currentColor"/>
  <circle cx="300" cy="210" r="4.5" fill="currentColor"/>
  <text x="40" y="236" font-size="14" text-anchor="middle" fill="currentColor">0</text>
  <text x="160" y="236" font-size="16" text-anchor="middle" fill="currentColor">y</text>
  <text x="300" y="236" font-size="16" text-anchor="middle" fill="currentColor">x</text>
</svg>
```

The adjunction $(a + x) \geq y \Leftrightarrow a \geq (x \multimap y)$ then reads: a budget of $a$ on top of $x$ covers $y$ exactly when $a$ alone covers the shortfall $\max(0, y - x)$. (Remember Cost's order is reversed: on the number line "$a + x$ covers $y$" is $a + x$ landing *at or past* $y$.)

The striking part is the direction of definition. Cost's monoid gives only **addition** — there is no subtraction in the structure. But because Cost is *closed*, the hom-element *is* a subtraction operation, built purely from the order ($\geq$) and addition ($+$). This is the "internalization" idea made concrete: closure lets the preorder express an operation that was not in its original vocabulary.
