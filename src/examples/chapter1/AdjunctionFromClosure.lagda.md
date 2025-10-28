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
module examples.chapter1.AdjunctionFromClosure where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter1.ClosureOperator using (ClosureOperator)
open import definitions.chapter1.GaloisConnection using (GaloisConnection)
open import definitions.chapter1.MonotoneMap using (Monotonic; _⇒_)
```

## The Example

From a closure operator j on preorder P, we construct a Galois connection between P and the preorder of fixed points.

```agda
module ConstructAdjunction (P : Preorder) (closure : ClosureOperator P) where
  open Preorder P renaming (Carrier to A; _≤_ to _≤P_)
  open ClosureOperator closure

  -- The preorder of fixed points
  FixJPreorder : Preorder

  -- The Galois connection: P ⊣ fix j
  closure-adjunction : GaloisConnection P FixJPreorder
```

### Implementation

**Strategy:** Define fix j = { p ∈ P | j(p) ≅ p }, use j as left adjoint and inclusion as right adjoint.

```agda
  -- A fixed point of j is an element p where j(p) ≅ p
  IsFixedPoint : A → Set
  IsFixedPoint p = j p ≅ p

  -- The carrier of fix j: pairs (p, proof that p is a fixed point)
  FixJ : Set
  FixJ = Σ[ p ∈ A ] IsFixedPoint p

  -- The order on fix j: inherited from P
  _≤fix_ : FixJ → FixJ → Set
  (p , _) ≤fix (q , _) = p ≤P q

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
  j-is-fixed-point : ∀ (p : A) → IsFixedPoint (j p)
  j-is-fixed-point p = idempotent p

  -- The left adjoint sends p to j(p)
  left-adjoint-fn : A → FixJ
  left-adjoint-fn p = (j p , j-is-fixed-point p)

  left-adjoint-monotonic : Monotonic _≤P_ _≤fix_ left-adjoint-fn
  left-adjoint-monotonic p≤q = j-monotonic p≤q

  left-adjoint : P ⇒ FixJPreorder
  left-adjoint = (left-adjoint-fn , left-adjoint-monotonic)

  -- The right adjoint is the inclusion map
  right-adjoint-fn : FixJ → A
  right-adjoint-fn (p , _) = p

  right-adjoint-monotonic : Monotonic _≤fix_ _≤P_ right-adjoint-fn
  right-adjoint-monotonic {x} {y} p≤q = p≤q

  right-adjoint : FixJPreorder ⇒ P
  right-adjoint = (right-adjoint-fn , λ {x} {y} → right-adjoint-monotonic {x} {y})

  -- Forward: j(p) ≤ q → p ≤ q (use extensivity and transitivity)
  forward : ∀ {p : A} {q : FixJ} → left-adjoint-fn p ≤fix q → p ≤P right-adjoint-fn q
  forward {p} {q , _} jp≤q = transitive (extensive p) jp≤q

  -- Backward: p ≤ q → j(p) ≤ q (use monotonicity and q being fixed)
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

## Summary

This establishes one direction of the **Galois connection ⟷ closure operator correspondence**:

- Exercise 1.111: Galois connection f ⊣ g ⟹ closure operator g∘f
- Example 1.114 (this): Closure operator j ⟹ Galois connection P ⊣ fix j

Together they show these are two perspectives on the same structure!
