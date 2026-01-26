---
layout: agda
title: "Joins iff Meets"
section: "Propositions"
chapter: 2
number: 72
---

# All Joins iff All Meets

## Textbook Statement

**Proposition 2.67.** Let $\mathcal{P} = (P, \leq)$ be a preorder. It has all joins iff it has all meets.

## Proof Sketch

The joins in $\mathcal{P}$ are the meets in $\mathcal{P}^{\text{op}}$, so the two claims are dual. It suffices to show that if $\mathcal{P}$ has all joins then it has all meets.

Suppose $\mathcal{P}$ has all joins and suppose that $A \subseteq \mathcal{P}$ is a subset for which we want the meet. Consider the set $M_A := \{p \in P \mid p \leq a \text{ for all } a \in A\}$ of elements below everything in $A$. Let $m_A := \bigvee_{p \in M_A} p$ be their join. We claim that $m_A$ is a meet for $A$.

1. For any $a \in A$, we have $m_A \leq a$: since all $p \in M_A$ satisfy $p \leq a$, so does their join $m_A$.
2. For any $m'$ with $m' \leq a$ for all $a \in A$, we have $m' \leq m_A$: every such $m'$ is an element of $M_A$, and $m_A$ is their join.

## Agda Setup

```agda
module propositions.chapter2.JoinsIffMeets where

open import definitions.chapter1.Preorder using (Preorder)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
```

## Definitions

```agda
-- A preorder has all joins
record HasAllJoins (P : Preorder) : Set₁ where
  open Preorder P

  field
    ⋁ : {I : Set} → (I → Carrier) → Carrier
    join-ub : ∀ {I : Set} {a : I → Carrier} {i : I} → a i ≤ ⋁ a
    join-lub : ∀ {I : Set} {a : I → Carrier} {b : Carrier}
             → (∀ i → a i ≤ b) → ⋁ a ≤ b

-- A preorder has all meets
record HasAllMeets (P : Preorder) : Set₁ where
  open Preorder P

  field
    ⋀ : {I : Set} → (I → Carrier) → Carrier
    meet-lb : ∀ {I : Set} {a : I → Carrier} {i : I} → ⋀ a ≤ a i
    meet-glb : ∀ {I : Set} {a : I → Carrier} {b : Carrier}
             → (∀ i → b ≤ a i) → b ≤ ⋀ a
```

## Construction of Meets from Joins

```agda
module JoinsToMeets (P : Preorder) (J : HasAllJoins P) where
  open Preorder P
  open HasAllJoins J

  -- The set of lower bounds of A
  -- M_A = {p ∈ P | p ≤ a for all a ∈ A}
  LowerBounds : {I : Set} → (I → Carrier) → Set
  LowerBounds {I} a = Σ[ p ∈ Carrier ] (∀ (i : I) → p ≤ a i)

  -- The meet is the join of all lower bounds
  meet : {I : Set} → (I → Carrier) → Carrier
  meet a = ⋁ {I = LowerBounds a} proj₁

  -- The meet is a lower bound
  meet-is-lb : ∀ {I : Set} {a : I → Carrier} {i : I} → meet a ≤ a i
  meet-is-lb {I} {a} {i} = join-lub (λ lb → proj₂ lb i)

  -- The meet is the greatest lower bound
  meet-is-glb : ∀ {I : Set} {a : I → Carrier} {b : Carrier}
              → (∀ i → b ≤ a i) → b ≤ meet a
  meet-is-glb {I} {a} {b} b-is-lb = join-ub {i = b , b-is-lb}

  -- Package it up
  hasAllMeets : HasAllMeets P
  hasAllMeets = record
    { ⋀ = meet
    ; meet-lb = meet-is-lb
    ; meet-glb = meet-is-glb
    }
```

## Interpretation

In particular, a quantale has all meets AND all joins, even though we only define it to have all joins. This is because the meet can always be constructed as "the join of all lower bounds."

This result is very useful: it means we don't need to separately postulate the existence of meets when defining quantales.
