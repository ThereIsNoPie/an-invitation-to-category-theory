---
layout: agda
title: "Monotone Identity and Composition"
section: "Propositions"
chapter: 1
number: 65
---

# Monotone Identity and Composition

## Textbook Definition

**Proposition 1.65.** For any preorder (P, ≤P), the identity function is monotone. If (Q, ≤Q) and (R, ≤R) are preorders and f : P → Q and g : Q → R are monotone, then (g ∘ f) : P → R is also monotone.

## Agda Setup

```agda
module propositions.chapter1.MonotoneIdentityComposition where

open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (id; _∘_)

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter1.MonotoneMap using (Monotonic; _⇒_)
```

## Proposition

```agda
monotone-id : (P : Preorder) → P ⇒ P

monotone-∘ : {P Q R : Preorder} → (f : P ⇒ Q) → (g : Q ⇒ R) → P ⇒ R
```

## Proof: Part 1 (Identity is Monotone)

The identity function preserves order trivially: if x ≤ y, then x ≤ y.

```agda
monotone-id P = id , preserves-order
  where
    open Preorder P

    preserves-order : Monotonic _≤_ _≤_ id
    preserves-order x≤y = x≤y
```

## Proof: Part 2 (Composition of Monotone Maps is Monotone)

If f preserves order from P to Q, and g preserves order from Q to R, then g ∘ f preserves order from P to R.

**Strategy:** Given x ≤P y, we have f(x) ≤Q f(y) (by f monotone), and then g(f(x)) ≤R g(f(y)) (by g monotone).

```agda
monotone-∘ {P} {Q} {R} (f , f-mono) (g , g-mono) = (g ∘ f) , preserves-order
  where
    open Preorder P renaming (_≤_ to _≤P_)
    open Preorder Q renaming (_≤_ to _≤Q_)
    open Preorder R renaming (_≤_ to _≤R_)

    preserves-order : Monotonic _≤P_ _≤R_ (g ∘ f)
    preserves-order {x} {y} x≤y =
      let fx≤fy : f x ≤Q f y
          fx≤fy = f-mono x≤y

          gfx≤gfy : g (f x) ≤R g (f y)
          gfx≤gfy = g-mono fx≤fy
      in gfx≤gfy
```
