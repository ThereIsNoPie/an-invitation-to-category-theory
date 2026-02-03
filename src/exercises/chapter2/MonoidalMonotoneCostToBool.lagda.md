---
layout: agda
title: "Monoidal Monotone from Cost to Bool"
section: "Exercises"
chapter: 2
number: 28
---

# Exercise 2.28: Monoidal Monotone from Cost to Bool

## Textbook Exercise

**Exercise 2.28.** Let Bool and Cost be as above, and consider the following quasi-inverse functions d, u : [0, ∞] → B defined as follows:

d(x) := { false if x > 0, true if x = 0 }

u(x) := { false if x = ∞, true if x < ∞ }

1. Is d monotonic?
2. Does d satisfy conditions (a) and (b) of Definition 2.25?
3. Is d strict?
4. Is u monotonic?
5. Does u satisfy conditions (a) and (b) of Definition 2.25?
6. Is u strict?

## Agda Setup

```agda
module exercises.chapter2.MonoidalMonotoneCostToBool where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter1.MonotoneMap using (Monotonic)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import definitions.chapter2.MonoidalMonotone
  using (IsMonoidalMonotone; IsStrictMonoidalMonotone)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-mono-≤; ≤-trans; ≤-refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

-- Import definitions from Exercise 2.27
open import exercises.chapter2.MonoidalMonotoneBoolToCost using
  ( _≤Bool_; false≤false; false≤true; true≤true
  ; ≤Bool-refl; ≤Bool-trans
  ; Bool-preorder; Bool-monoidal; Bool-monoidal-structure
  ; ℕ∞; fin; ∞
  ; _≥∞_; ∞≥∞; ∞≥fin; fin≥fin
  ; ≥∞-refl; ≥∞-trans
  ; _+∞_
  ; +∞-mono; +∞-identityˡ; +∞-identityʳ; +∞-assoc; +∞-comm
  ; Cost-preorder; Cost; Cost-monoidal-structure
  )
```

## Problem

Define the functions d and u from Cost to Bool, and verify their properties.

```agda
-- The "down" function: d(x) = true if x = 0, false if x > 0
d : ℕ∞ → Bool
d (fin zero) = true
d (fin (suc n)) = false
d ∞ = false

-- The "up" function: u(x) = true if x < ∞, false if x = ∞
u : ℕ∞ → Bool
u (fin n) = true
u ∞ = false
```

## Part 1

**Question:** Is d monotonic?

```agda
d-monotonic : Monotonic _≥∞_ _≤Bool_ d
```

## Solution

**Strategy:** Verify monotonicity by case analysis on the ordering relation.

```agda
d-monotonic ∞≥∞ = false≤false
d-monotonic {∞} {fin zero} ∞≥fin = false≤true
d-monotonic {∞} {fin (suc n)} ∞≥fin = false≤false
d-monotonic {fin zero} {fin zero} (fin≥fin z≤n) = true≤true
d-monotonic {fin (suc m)} {fin zero} (fin≥fin z≤n) = false≤true
d-monotonic {fin (suc m)} {fin (suc n)} (fin≥fin (s≤s p)) = false≤false
```

**Answer:** Yes, d is monotonic.

## Part 2

**Question:** Does d satisfy conditions (a) and (b) of Definition 2.25?

```agda
d-preserves-unit : true ≤Bool d (fin 0)
d-preserves-mult : ∀ {x y : ℕ∞} → (d x ∧ d y) ≤Bool d (x +∞ y)
d-is-monoidal-monotone : IsMonoidalMonotone Cost Bool-monoidal d
```

## Solution

**Strategy:** Verify unit preservation (condition a) and multiplication preservation (condition b) by direct computation and case analysis.

```agda
-- Condition (a): I_Bool ≤_Bool d(I_Cost)
-- i.e., true ≤Bool d(fin 0) = true
d-preserves-unit = true≤true

-- Condition (b): d(x) ∧ d(y) ≤Bool d(x +∞ y)
d-preserves-mult {fin zero} {fin zero} = true≤true
d-preserves-mult {fin zero} {fin (suc n)} = false≤false
d-preserves-mult {fin zero} {∞} = false≤false
d-preserves-mult {fin (suc m)} {fin zero} = false≤false
d-preserves-mult {fin (suc m)} {fin (suc n)} = false≤false
d-preserves-mult {fin (suc m)} {∞} = false≤false
d-preserves-mult {∞} {fin zero} = false≤false
d-preserves-mult {∞} {fin (suc n)} = false≤false
d-preserves-mult {∞} {∞} = false≤false

d-is-monoidal-monotone = record
  { monotone = d-monotonic
  ; preserves-unit = d-preserves-unit
  ; preserves-mult = d-preserves-mult
  }
```

**Answer:** Yes, d satisfies conditions (a) and (b) of Definition 2.25.

## Part 3

**Question:** Is d strict?

```agda
d-preserves-mult-≡ : ∀ {x y : ℕ∞} → (d x ∧ d y) ≡ d (x +∞ y)
d-is-strict : IsStrictMonoidalMonotone Cost Bool-monoidal d
```

## Solution

**Strategy:** Check if the unit and multiplication preservation hold with equality (not just inequality).

```agda
-- Check if d(x) ∧ d(y) = d(x +∞ y) for all x, y
d-preserves-mult-≡ {fin zero} {fin zero} = refl
d-preserves-mult-≡ {fin zero} {fin (suc n)} = refl
d-preserves-mult-≡ {fin zero} {∞} = refl
d-preserves-mult-≡ {fin (suc m)} {fin zero} = refl
d-preserves-mult-≡ {fin (suc m)} {fin (suc n)} = refl
d-preserves-mult-≡ {fin (suc m)} {∞} = refl
d-preserves-mult-≡ {∞} {fin zero} = refl
d-preserves-mult-≡ {∞} {fin (suc n)} = refl
d-preserves-mult-≡ {∞} {∞} = refl

d-is-strict = record
  { monotone = d-monotonic
  ; preserves-unit-≡ = refl  -- true = d(fin 0)
  ; preserves-mult-≡ = d-preserves-mult-≡
  }
```

**Answer:** Yes, d is strict.

## Part 4

**Question:** Is u monotonic?

```agda
u-monotonic : Monotonic _≥∞_ _≤Bool_ u
```

## Solution

**Strategy:** Verify monotonicity by case analysis on the ordering relation.

```agda
u-monotonic ∞≥∞ = false≤false
u-monotonic ∞≥fin = false≤true
u-monotonic (fin≥fin _) = true≤true
```

**Answer:** Yes, u is monotonic.

## Part 5

**Question:** Does u satisfy conditions (a) and (b) of Definition 2.25?

```agda
u-preserves-unit : true ≤Bool u (fin 0)
u-preserves-mult : ∀ {x y : ℕ∞} → (u x ∧ u y) ≤Bool u (x +∞ y)
u-is-monoidal-monotone : IsMonoidalMonotone Cost Bool-monoidal u
```

## Solution

**Strategy:** Verify unit preservation (condition a) and multiplication preservation (condition b) by direct computation and case analysis.

```agda
-- Condition (a): I_Bool ≤_Bool u(I_Cost)
-- i.e., true ≤Bool u(fin 0) = true
u-preserves-unit = true≤true

-- Condition (b): u(x) ∧ u(y) ≤Bool u(x +∞ y)
u-preserves-mult {fin m} {fin n} = true≤true
u-preserves-mult {fin m} {∞} = false≤false
u-preserves-mult {∞} {fin n} = false≤false
u-preserves-mult {∞} {∞} = false≤false

u-is-monoidal-monotone = record
  { monotone = u-monotonic
  ; preserves-unit = u-preserves-unit
  ; preserves-mult = u-preserves-mult
  }
```

**Answer:** Yes, u satisfies conditions (a) and (b) of Definition 2.25.

## Part 6

**Question:** Is u strict?

```agda
u-preserves-mult-≡ : ∀ {x y : ℕ∞} → (u x ∧ u y) ≡ u (x +∞ y)
u-is-strict : IsStrictMonoidalMonotone Cost Bool-monoidal u
```

## Solution

**Strategy:** Check if the unit and multiplication preservation hold with equality (not just inequality).

```agda
-- Check if u(x) ∧ u(y) = u(x +∞ y) for all x, y
u-preserves-mult-≡ {fin m} {fin n} = refl
u-preserves-mult-≡ {fin m} {∞} = refl
u-preserves-mult-≡ {∞} {fin n} = refl
u-preserves-mult-≡ {∞} {∞} = refl

u-is-strict = record
  { monotone = u-monotonic
  ; preserves-unit-≡ = refl  -- true = u(fin 0)
  ; preserves-mult-≡ = u-preserves-mult-≡
  }
```

**Answer:** Yes, u is strict.

## Summary

Both d and u are **strict monoidal monotones** from Cost to Bool:

- **d (the "down" function)**: Maps 0 to true and all positive values (including ∞) to false. It detects whether a cost is exactly zero.

- **u (the "up" function)**: Maps all finite values to true and ∞ to false. It detects whether a cost is finite.

These functions are "quasi-inverses" in the sense that they provide different ways to collapse the richer structure of Cost (with its many elements) back into the simpler Bool structure (with just two elements). Both preserve the monoidal structure strictly, meaning the equations hold on the nose, not just up to the ordering.
```
