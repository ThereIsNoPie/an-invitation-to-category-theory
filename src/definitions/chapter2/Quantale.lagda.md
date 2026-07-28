---
layout: agda
title: "Quantale"
section: "Definitions"
chapter: 2
number: 66
---

# Quantale

## Textbook Definition

**Definition 2.66.** A *unital commutative quantale* is a symmetric monoidal closed preorder $\mathcal{V} = (V, \leq, I, \otimes, \multimap)$ that has all joins: $\bigvee A$ exists for every $A \subseteq V$. In particular, we often denote the empty join by $0 := \bigvee \varnothing$.

## Agda Setup

```agda
module definitions.chapter2.Quantale where

open import definitions.chapter2.MonoidalClosed
  using (MonoidalClosedPreorder; IsMonoidalClosed)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
```

## A Small Example

Before the general definition, here is the smallest interesting quantale: the powerset $P(\{a,b\})$ ordered by $\subseteq$ (Exercise 2.70). The monoidal product is intersection $\cap$, so the unit $I$ is the *top* element $\{a,b\}$; joins are unions, and the empty join $0$ is the *bottom* element $\varnothing$. Every ingredient of the definition is visible in one picture:

```svg
<svg viewBox="0 0 620 310" role="img" aria-label="Hasse diagram of the powerset quantale on {a,b}: empty set at the bottom, {a} and {b} in the middle, {a,b} at the top, with the quantale structure labelled alongside">
  <text x="170" y="56" font-size="16" text-anchor="middle" fill="currentColor">{a,b}</text>
  <text x="90" y="161" font-size="16" text-anchor="middle" fill="currentColor">{a}</text>
  <text x="250" y="161" font-size="16" text-anchor="middle" fill="currentColor">{b}</text>
  <text x="170" y="266" font-size="16" text-anchor="middle" fill="currentColor">∅</text>
  <line x1="155" y1="245" x2="102" y2="176" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="185" y1="245" x2="238" y2="176" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="102" y1="141" x2="153" y2="71" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="238" y1="141" x2="187" y2="71" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <text x="330" y="56" font-size="16" text-anchor="start" fill="currentColor">I = {a,b} — unit, since ⊗ = ∩</text>
  <text x="330" y="161" font-size="16" text-anchor="start" fill="var(--agda-function)">{a} ∨ {b} = {a,b} — joins are ∪</text>
  <text x="330" y="266" font-size="16" text-anchor="start" fill="currentColor">0 = ⋁∅ = ∅ — the empty join</text>
</svg>
```

Arrows point up the order $\subseteq$. Note the join $\{a\} \vee \{b\} = \{a,b\}$: neither $\{a\}$ nor $\{b\}$ is above the other, so their join is the least element above *both* — that is what "has all joins" buys you. The closed structure is $B \multimap C = (S \setminus B) \cup C$, so this is a symmetric monoidal closed preorder with all joins: a quantale.

## All Joins

A preorder has all joins if every subset has a join. We model this using an indexed join over any index set.

```agda
-- A preorder has all joins if for every index set I and family A : I → V,
-- the join ⋁ᵢ A(i) exists
record HasAllJoins (V : SymmetricMonoidalPreorder) : Set₁ where
  open SymmetricMonoidalPreorder V

  field
    -- The join operation, indexed by any set
    ⋁ : {I : Set} → (I → Carrier) → Carrier

    -- Join is an upper bound: a(i) ≤ ⋁ a for all i
    join-ub : ∀ {I : Set} {a : I → Carrier} {i : I} → a i ≤ ⋁ a

    -- Join is the least upper bound: if b is an upper bound, then ⋁ a ≤ b
    join-lub : ∀ {I : Set} {a : I → Carrier} {b : Carrier}
             → (∀ i → a i ≤ b) → ⋁ a ≤ b

  -- The empty join (indexed by the empty type)
  𝟘 : Carrier
  𝟘 = ⋁ {I = ⊥} (λ ())

  -- Binary join
  _∨_ : Carrier → Carrier → Carrier
  x ∨ y = ⋁ {I = Bool} (λ { true → x ; false → y })
```

## Agda Formalization

```agda
-- A unital commutative quantale
record Quantale : Set₁ where
  field
    closedPreorder : MonoidalClosedPreorder
    hasAllJoins : HasAllJoins (MonoidalClosedPreorder.base closedPreorder)

  open MonoidalClosedPreorder closedPreorder public
  open HasAllJoins hasAllJoins public
```

## Properties

From Proposition 2.64(b), we know that the monoidal product distributes over joins in a quantale.

```agda
module QuantaleProperties (Q : Quantale) where
  open Quantale Q

  -- The monoidal product distributes over joins (follows from the adjunction)
  -- v ⊗ (⋁ᵢ aᵢ) ≅ ⋁ᵢ (v ⊗ aᵢ)
  -- This is because (-⊗v) is a left adjoint, and left adjoints preserve joins
  postulate
    ⊗-distributes-⋁ : ∀ {I : Set} {a : I → Carrier} {v : Carrier}
                    → (v ⊗ ⋁ a) ≤ ⋁ (λ i → v ⊗ a i)
```

## Interpretation

A quantale is a monoidal closed preorder with "enough joins" to perform operations like matrix multiplication. The key examples are:

- **Bool**: has all joins (∨ is boolean OR, the empty join is false)
- **Cost**: has all joins (∨ is infimum/min, the empty join is ∞)

The distributivity of ⊗ over joins is crucial for matrix multiplication to work correctly.
