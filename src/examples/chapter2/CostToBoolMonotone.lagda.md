---
layout: agda
title: "Cost to Bool Monoidal Monotone"
section: "Examples"
chapter: 2
number: 45
---

# Cost to Bool Monoidal Monotone

## Textbook Description

**Example 2.45.** Consider the function $f : [0,\infty] \to \{\mathsf{true}, \mathsf{false}\}$ given by:

- $f(x) = \mathsf{true}$ if $x = 0$
- $f(x) = \mathsf{false}$ if $x > 0$

It is easy to check that $f$ is monotonic and that $f$ preserves the monoidal product and monoidal unit; that is, it's easy to show that $f$ is a monoidal monotone.

Thus $f$ lets us convert Lawvere metric spaces into preorders.

## Agda Setup

```agda
module examples.chapter2.CostToBoolMonotone where

open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import definitions.chapter2.MonoidalMonotone
  using (MonoidalMonotone; IsMonoidalMonotone)
open import examples.chapter2.Cost using (Cost; [0,∞]; 0∞; ∞; _≥_; _+ℝ_)
open import examples.chapter2.BoolAnd using (Bool-SMP; _≤𝔹_; ≤-refl)
open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Product using (_,_)
```

## The Function

```agda
postulate
  -- Decision procedure: is x equal to 0?
  _≟0 : [0,∞] → Bool
  ≟0-spec-zero : 0∞ ≟0 ≡ true

-- f(x) = true if x = 0, false if x > 0
f : [0,∞] → Bool
f x = x ≟0
```

## Monoidal Monotone Properties

```agda
postulate
  -- Monotonicity: x ≥ y implies f(x) ≤ f(y)
  -- (larger costs map to false, 0 maps to true, and false ≤ true)
  f-monotone : ∀ {x y : [0,∞]} → x ≥ y → (f x) ≤𝔹 (f y)

  -- Preserves multiplication: (f x ∧ f y) ≤ f(x + y)
  f-preserves-mult : ∀ {x y : [0,∞]} → (f x ∧ f y) ≤𝔹 f (x +ℝ y)

-- Preserves unit: true ≤ f(0)
f-preserves-unit : true ≤𝔹 f 0∞
f-preserves-unit = subst (true ≤𝔹_) (sym ≟0-spec-zero) ≤-refl
```

## The Monoidal Monotone

```agda
Cost→Bool : MonoidalMonotone Cost Bool-SMP
Cost→Bool = f , record
  { monotone = f-monotone
  ; preserves-unit = f-preserves-unit
  ; preserves-mult = f-preserves-mult
  }
```

## Applying Change of Base

Using Construction 2.44, we can convert any Lawvere metric space (Cost-category) into a preorder (Bool-category).

```agda
open import definitions.chapter2.ChangeOfBase using (changeOfBase)
open import definitions.chapter2.VCategory using (VCategory)
open import definitions.chapter2.LawvereMetricSpace using (LawvereMetricSpace)

-- Convert any Lawvere metric space to a preorder
toPreorder : LawvereMetricSpace → VCategory Bool-SMP
toPreorder = changeOfBase Cost→Bool
```

## Interpretation

This monoidal monotone "forgets distances" — it only remembers whether two points are the same (distance 0) or different (distance > 0). When applied to a Lawvere metric space via change of base, it produces the underlying preorder where $x \leq y$ iff $d(x,y) = 0$.
