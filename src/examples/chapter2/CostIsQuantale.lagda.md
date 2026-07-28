---
layout: agda
title: "Cost is a Quantale"
section: "Examples"
chapter: 2
number: 67
---

# Cost is a Quantale

## Textbook Description

**Example 2.67.** In Example 2.60, we saw that Cost is monoidal closed. To check whether Cost is a quantale, we take an arbitrary set of elements $A \subseteq [0, \infty]$ and ask if it has a join $\bigvee A$. To be a join, it needs to satisfy:

(a) $a \geq \bigvee A$ for all $a \in A$, and
(b) if $b \in [0, \infty]$ is any element such that $a \geq b$ for all $a \in A$, then $\bigvee A \geq b$.

In fact we can define such a join: it is typically called the *infimum*, or greatest lower bound, of $A$.

For example, if $A = \{2, 3\}$ then $\bigvee A = 2$. We have joins for infinite sets too: if $B = \{2.5, 2.05, 2.005, \ldots\}$, its infimum is $2$. Finally, the empty join $\bigvee \varnothing = \infty$ (the largest element in the reversed order).

Thus indeed $([0, \infty], \geq)$ has all joins, so Cost is a quantale.

## Agda Setup

```agda
module examples.chapter2.CostIsQuantale where

open import definitions.chapter2.Quantale using (Quantale; HasAllJoins)
open import definitions.chapter2.MonoidalClosed using (MonoidalClosedPreorder)
open import examples.chapter2.CostIsMonoidalClosed using (Cost-MCP)
open import examples.chapter2.Cost using (Cost; [0,∞]; 0∞; ∞; _≥_)
```

## Joins in Cost

In Cost with the $\geq$ order:
- The join of a set is its infimum (greatest lower bound in the usual order)
- The empty join is $\infty$ (the bottom element in Cost's order)
- Binary join is minimum

```agda
postulate
  -- The infimum (greatest lower bound) exists for any subset of [0,∞]
  inf : {I : Set} → (I → [0,∞]) → [0,∞]

  -- Infimum is below everything: for all i, a(i) ≥ inf a
  inf-lb : ∀ {I : Set} {a : I → [0,∞]} {i : I} → a i ≥ inf a

  -- Infimum is greatest lower bound: if b ≤ all a(i), then b ≤ inf a
  inf-glb : ∀ {I : Set} {a : I → [0,∞]} {b : [0,∞]}
          → (∀ i → a i ≥ b) → inf a ≥ b
```

## Cost Has All Joins

```agda
Cost-has-joins : HasAllJoins Cost
Cost-has-joins = record
  { ⋁ = inf
  ; join-ub = inf-lb
  ; join-lub = inf-glb
  }
```

## Cost as a Quantale

```agda
Cost-Quantale : Quantale
Cost-Quantale = record
  { closedPreorder = Cost-MCP
  ; hasAllJoins = Cost-has-joins
  }
```

## Interpretation

The joins in Cost work "backwards" compared to the usual order on real numbers because Cost uses $\geq$ as its order:

| Usual order $\leq$ | Cost order $\geq$ |
|-------------------|-------------------|
| Supremum (lub)    | Join in Cost      |
| Infimum (glb)     | Meet in Cost      |

So the "join" of $\{2, 3\}$ in Cost is $\min(2, 3) = 2$, because $2$ is the element that is $\geq$ both 2 and 3, and is the largest such element.

The empty join in Cost is $\infty$ because $\infty \geq x$ for all $x$.
