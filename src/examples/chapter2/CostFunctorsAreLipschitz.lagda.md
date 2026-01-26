---
layout: agda
title: "Cost-Functors are Lipschitz Functions"
section: "Examples"
chapter: 2
number: 51
---

# Cost-Functors are Lipschitz Functions

## Textbook Description

**Example 2.49.** Lawvere metric spaces are Cost-categories. The definition of Cost-functor should hopefully return a nice notion—a "friend"—from the theory of metric spaces, and it does: it recovers the notion of Lipschitz function.

A Lipschitz (or more precisely, 1-Lipschitz) function is one under which the distance between any pair of points does not increase. That is, given Lawvere metric spaces $(X, d_X)$ and $(Y, d_Y)$, a Cost-functor between them is a function $F : X \to Y$ such that for every $x_1, x_2 \in X$ we have $d_X(x_1, x_2) \geq d_Y(F(x_1), F(x_2))$.

## Agda Setup

```agda
module examples.chapter2.CostFunctorsAreLipschitz where

open import definitions.chapter2.VCategory using (VCategory)
open import definitions.chapter2.VFunctor using (VFunctor; IsVFunctor)
open import definitions.chapter2.LawvereMetricSpace using (LawvereMetricSpace)
open import examples.chapter2.Cost using (Cost; [0,∞]; _≥_)
open import Data.Product using (_,_)
```

## 1-Lipschitz Functions

A function is 1-Lipschitz if it doesn't increase distances.

```agda
-- A function between Lawvere metric spaces is 1-Lipschitz if
-- d_X(x₁, x₂) ≥ d_Y(f(x₁), f(x₂)) for all x₁, x₂
Is1Lipschitz : (X Y : LawvereMetricSpace)
             → (VCategory.Ob X → VCategory.Ob Y)
             → Set
Is1Lipschitz X Y f = ∀ {x₁ x₂} → d-X x₁ x₂ ≥ d-Y (f x₁) (f x₂)
  where
    d-X = VCategory.hom X
    d-Y = VCategory.hom Y
```

## Cost-Functor = 1-Lipschitz

The V-functor condition for V = Cost says exactly that the function is 1-Lipschitz.

```agda
-- A Cost-functor is exactly a 1-Lipschitz function
-- The V-functor condition: X(x₁,x₂) ≤ Y(f(x₁),f(x₂)) in Cost
-- Since Cost has reversed order (≥), this becomes: d_X(x₁,x₂) ≥ d_Y(f(x₁),f(x₂))

-- From Cost-functor, extract the 1-Lipschitz property
Cost-Functor→1Lipschitz : {X Y : LawvereMetricSpace}
                        → (F : VFunctor X Y)
                        → Is1Lipschitz X Y (Data.Product.proj₁ F)
Cost-Functor→1Lipschitz (f , f-is) = IsVFunctor.preserves-hom f-is

-- From 1-Lipschitz function, construct a Cost-functor
1Lipschitz→Cost-Functor : {X Y : LawvereMetricSpace}
                        → (f : VCategory.Ob X → VCategory.Ob Y)
                        → Is1Lipschitz X Y f
                        → VFunctor X Y
1Lipschitz→Cost-Functor f lip = f , record { preserves-hom = lip }
```

## Interpretation

This example demonstrates that enriched category theory unifies different mathematical concepts:

| V | V-category | V-functor |
|---|------------|-----------|
| Bool | Preorder | Monotone map |
| Cost | Lawvere metric space | 1-Lipschitz function |

The abstract definition of V-functor specializes to familiar notions depending on the choice of enriching category V.
