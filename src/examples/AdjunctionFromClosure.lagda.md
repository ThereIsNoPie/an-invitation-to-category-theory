---
layout: agda
title: "Adjunctions from Closure Operators"
section: "Examples"
chapter: 1
number: 114
---

# Adjunctions from Closure Operators

## Textbook Description

**Example 1.114 (Adjunctions from closure operators).** Just as every adjunction gives rise to a closure operator, from every closure operator we may construct an adjunction.

Let P be a preorder and let j : P → P be a closure operator. We can define a preorder fix j to have elements the fixed points of j; that is,

fix j := { p ∈ P | j(p) ≅ p }.

This is a subset of P and inherits an order as a result; hence fix j is a sub-preorder of P. Note that j(p) is a fixed point for all p ∈ P, since j(j(p)) ≅ j(p).

We define an adjunction with left adjoint j : P → fix j sending p to j(p), and right adjoint g : fix j → P simply the inclusion of the sub-preorder. To see it's really an adjunction, we need to see that for any p ∈ P and q ∈ fix j, we have j(p) ≤ q if and only if p ≤ q. Let's check it. Since p ≤ j(p), we have that j(p) ≤ q implies p ≤ q by transitivity. Conversely, since q is a fixed point, p ≤ q implies j(p) ≤ j(q) ≅ q.

## Agda Setup

```agda
module examples.AdjunctionFromClosure where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import definitions.Preorder using (Preorder; IsPreorder)
open import definitions.ClosureOperator using (ClosureOperator)
open import definitions.GaloisConnection using (GaloisConnection)
open import definitions.MonotoneMap using (Monotonic; _⇒_)
```

## The Example

Given a closure operator j on a preorder P, we construct an adjunction between P and the subpreorder of fixed points.

### Key Type Definitions

```agda
module ConstructAdjunction (P : Preorder) (closure : ClosureOperator P) where
  open Preorder P renaming (Carrier to A; _≤_ to _≤P_)
  open ClosureOperator closure

  -- A fixed point of j is an element p where j(p) ≅ p
  IsFixedPoint : A → Set
  IsFixedPoint p = (j p ≤P p) × (p ≤P j p)

  -- The carrier of fix j: pairs (p, proof that p is a fixed point)
  FixJ : Set
  FixJ = Σ[ p ∈ A ] IsFixedPoint p

  -- The order on fix j: inherited from P
  _≤fix_ : FixJ → FixJ → Set
  (p , _) ≤fix (q , _) = p ≤P q

  -- The preorder of fixed points
  FixJPreorder : Preorder
```

## The Subpreorder of Fixed Points

We construct the preorder structure on fixed points.

```agda
  -- Key observation: j(p) is always a fixed point
  j-is-fixed-point : ∀ (p : A) → IsFixedPoint (j p)
```

### Implementation

**Strategy:** Use the idempotence property of the closure operator to show j(p) is a fixed point, and inherit the preorder structure from P.

```agda
  -- fix j forms a preorder
  fixj-isPreorder : IsPreorder _≤fix_
  fixj-isPreorder = record
    { reflexive = reflexive
    ; transitive = transitive
    }

  FixJPreorder = record
    { Carrier = FixJ
    ; _≤_ = _≤fix_
    ; isPreorder = fixj-isPreorder
    }

  -- j(p) is always a fixed point because j(j(p)) ≅ j(p) by idempotence
  j-is-fixed-point p = idempotent p
```

## The Adjunction

We construct the left and right adjoints and verify the adjunction property.

```agda
  -- The left adjoint: P → fix j
  left-adjoint : P ⇒ FixJPreorder

  -- The right adjoint: fix j → P (inclusion)
  right-adjoint : FixJPreorder ⇒ P

  -- The Galois connection
  closure-adjunction : GaloisConnection P FixJPreorder
```

### Implementation

**Strategy:** The left adjoint sends p to j(p) (which is always a fixed point). The right adjoint is inclusion. The adjunction properties follow from extensivity and idempotence.

```agda
  -- The left adjoint sends p to j(p)
  left-adjoint-fn : A → FixJ
  left-adjoint-fn p = (j p , j-is-fixed-point p)

  left-adjoint-monotonic : Monotonic _≤P_ _≤fix_ left-adjoint-fn
  left-adjoint-monotonic p≤q = j-monotonic p≤q

  left-adjoint = (left-adjoint-fn , left-adjoint-monotonic)

  -- The right adjoint is the inclusion map
  right-adjoint-fn : FixJ → A
  right-adjoint-fn (p , _) = p

  right-adjoint-monotonic : Monotonic _≤fix_ _≤P_ right-adjoint-fn
  right-adjoint-monotonic {x} {y} p≤q = p≤q

  right-adjoint = (right-adjoint-fn , λ {x} {y} → right-adjoint-monotonic {x} {y})

  -- Proof of adjunction: j(p) ≤ q iff p ≤ q

  -- Forward direction: j(p) ≤ q → p ≤ q
  -- Since p ≤ j(p) (extensivity) and j(p) ≤ q, we get p ≤ q by transitivity
  forward : ∀ {p : A} {q : FixJ} → left-adjoint-fn p ≤fix q → p ≤P right-adjoint-fn q
  forward {p} {q , _} jp≤q = transitive (extensive p) jp≤q

  -- Backward direction: p ≤ q → j(p) ≤ q
  -- Since q is a fixed point (j(q) ≅ q) and j is monotonic: p ≤ q → j(p) ≤ j(q) ≅ q
  backward : ∀ {p : A} {q : FixJ} → p ≤P right-adjoint-fn q → left-adjoint-fn p ≤fix q
  backward {p} {q , (jq≤q , q≤jq)} p≤q =
    transitive (j-monotonic p≤q) jq≤q

  -- The Galois connection
  closure-adjunction = record
    { f = left-adjoint-fn
    ; g = right-adjoint-fn
    ; f-g = λ {x} {y} → forward {x} {y}
    ; g-f = λ {x} {y} → backward {x} {y}
    }
```

## Interpretation

This construction demonstrates one direction of the fundamental correspondence between Galois connections and closure operators:

- **Exercise 1.111** (GaloisGivesClosure) shows that every Galois connection f ⊣ g gives a closure operator: the composition g∘f : P → P is a closure operator on P. This uses Proposition 1.101 (unit/counit) to prove extensivity and idempotence.

- **Example 1.114** (this example) shows the converse: every closure operator j : P → P gives rise to a Galois connection between P and the subpreorder of fixed points fix j.

The key insight is that:
1. The **fixed points** of j form a natural subpreorder fix j = { p ∈ P | j(p) ≅ p }
2. The closure operator j provides a **left adjoint** j : P → fix j (sending p ↦ j(p))
3. The **inclusion** g : fix j → P provides the right adjoint
4. The adjunction properties (j(p) ≤ q ⟺ p ≤ q) follow directly from:
   - Extensivity: p ≤ j(p)
   - Idempotence: j(j(p)) ≅ j(p), meaning j(p) is always a fixed point

Together, Exercise 1.111 and Example 1.114 establish that **Galois connections and closure operators are in bijective correspondence** - they are two perspectives on the same mathematical structure!

## Summary

Given `closure : ClosureOperator P`, we construct:
- `FixJPreorder`: The preorder of fixed points { p | j(p) ≅ p }
- `left-adjoint`: The map P → fix j sending p ↦ j(p)
- `right-adjoint`: The inclusion fix j → P
- `closure-adjunction`: The Galois connection between P and fix j

This construction is universal: every closure operator determines a unique adjunction in this way.
```
