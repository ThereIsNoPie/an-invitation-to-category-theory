---
layout: agda
title: "Apples and Buckets"
section: "Examples"
chapter: 1
number: 109
---

<!--
```agda
module examples.ApplesAndBuckets where

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_)
```
-->

# Example 1.109: Apples and Buckets

This example demonstrates a beautiful phenomenon in category theory: **a single function induces three different adjoint functors**. We'll use the intuitive metaphor of placing apples into buckets to understand these abstract concepts.

## The Setup

Imagine we have a collection of apples and a collection of buckets, and each apple is placed in exactly one bucket. This placement is represented by a function `f : Apples → Buckets`.

Now, we can ask questions about _subsets_ of apples and subsets of buckets. Given a subset of apples, which buckets are relevant? Given a subset of buckets, which apples are relevant? These questions lead to three different functors between powersets.

## Powersets and Inclusion

We represent subsets using the **powerset** construction. A subset of `X` is represented as a predicate `X → Set` (a function that says whether each element is in the subset).

```agda
Powerset : Set → Set₁
Powerset X = X → Set
```

Subset inclusion is defined as implication between predicates:

```agda
_⊆_ : {X : Set} → Powerset X → Powerset X → Set
_⊆_ S T = ∀ {x} → S x → T x
```

This says that `S ⊆ T` if whenever `x` is in `S`, then `x` is also in `T`.

## The Three Functors

Given a function `f : Apples → Buckets`, we can define three functors between the powersets `𝒫(Apples)` and `𝒫(Buckets)`:

```agda
module ApplesAndBucketsTheorem (Apples Buckets : Set) (f : Apples → Buckets) where

  A = Apples
  B = Buckets

  𝒫A = Powerset A
  𝒫B = Powerset B
```

### Functor 1: Pullback (f\*)

The **pullback** or **preimage** functor `f* : 𝒫B → 𝒫A` answers the question:

> _"Given a subset of buckets B', which apples go into those buckets?"_

```agda
  -- f*(B') = { a ∈ A | f(a) ∈ B' }
  f* : 𝒫B → 𝒫A
  f* B' a = B' (f a)
```

An apple `a` is in `f*(B')` if its bucket `f(a)` is in `B'`.

### Functor 2: Existential Image (f!)

The **existential image** functor `f! : 𝒫A → 𝒫B` answers:

> _"Given a subset of apples A', which buckets contain at least one of those apples?"_

```agda
  -- f!(A') = { b ∈ B | ∃a ∈ A'. f(a) = b }
  f! : 𝒫A → 𝒫B
  f! A' b = Σ[ a ∈ A ] (A' a × f a ≡ b)
```

A bucket `b` is in `f!(A')` if there exists some apple `a` in `A'` such that `f(a) = b`.

### Functor 3: Universal Image (f∗)

The **universal image** functor `f∗ : 𝒫A → 𝒫B` asks:

> _"Given a subset of apples A', which buckets contain only apples from A'?"_

```agda
  -- f∗(A') = { b ∈ B | ∀a. f(a) = b → a ∈ A' }
  f∗ : 𝒫A → 𝒫B
  f∗ A' b = ∀ {a} → f a ≡ b → A' a
```

A bucket `b` is in `f∗(A')` if every apple that goes into `b` is in `A'`.

## The Two Adjunctions

These three functors form two **adjoint pairs**. An adjunction `F ⊣ G` means that `F` and `G` are intimately related: `F(x) ≤ y` if and only if `x ≤ G(y)`.

### Adjunction 1: f! ⊣ f\*

The first adjunction states:

> _"All buckets containing apples from A' are in B' **if and only if** all apples in A' map to buckets in B'."_

Formally: **f!(A') ⊆ B' ⟺ A' ⊆ f\*(B')**

#### Forward direction (→)

If all buckets containing an apple from `A'` are in `B'`, then all apples in `A'` must map to buckets in `B'`:

```agda
  f!⊆→⊆f* : ∀ {A' B'} → f! A' ⊆ B' → A' ⊆ f* B'
  f!⊆→⊆f* f!A'⊆B' {a} a∈A' = f!A'⊆B' (a , a∈A' , refl)
```

**Proof intuition**: If `a` is in `A'`, then the bucket `f(a)` contains `a`, so `f(a)` is in `f!(A')`. By assumption, `f!(A') ⊆ B'`, so `f(a)` is in `B'`, which means `a` is in `f*(B')`.

#### Backward direction (←)

If all apples in `A'` map to buckets in `B'`, then all buckets containing an apple from `A'` are in `B'`:

```agda
  ⊆f*→f!⊆ : ∀ {A' B'} → A' ⊆ f* B' → f! A' ⊆ B'
  ⊆f*→f!⊆ A'⊆f*B' {b} (a , a∈A' , refl) = A'⊆f*B' a∈A'
```

**Proof intuition**: If bucket `b` is in `f!(A')`, then there exists some apple `a` in `A'` with `f(a) = b`. Since `a` is in `A'` and `A' ⊆ f*(B')`, we know `f(a)` is in `B'`, so `b` is in `B'`.

### Adjunction 2: f\* ⊣ f∗

The second adjunction states:

> _"All apples in buckets B' are in A' **if and only if** all buckets in B' contain only apples from A'."_

Formally: **f\*(B') ⊆ A' ⟺ B' ⊆ f∗(A')**

#### Forward direction (→)

If all apples in buckets `B'` are in `A'`, then every bucket in `B'` contains only apples from `A'`:

```agda
  f*⊆→⊆f∗ : ∀ {B' A'} → f* B' ⊆ A' → B' ⊆ f∗ A'
  f*⊆→⊆f∗ f*B'⊆A' {b} b∈B' {a} refl = f*B'⊆A' b∈B'
```

**Proof intuition**: If bucket `b` is in `B'` and apple `a` maps to `b` (i.e., `f(a) = b`), then `a` is in `f*(B')`. By assumption `f*(B') ⊆ A'`, so `a` is in `A'`.

#### Backward direction (←)

If every bucket in `B'` contains only apples from `A'`, then all apples in buckets `B'` are in `A'`:

```agda
  ⊆f∗→f*⊆ : ∀ {B' A'} → B' ⊆ f∗ A' → f* B' ⊆ A'
  ⊆f∗→f*⊆ B'⊆f∗A' {a} fa∈B' = B'⊆f∗A' fa∈B' refl
```

**Proof intuition**: If apple `a` is in `f*(B')`, then `f(a)` is in `B'`. Since `B' ⊆ f∗(A')`, every apple that maps to `f(a)` is in `A'`. In particular, `a` maps to `f(a)`, so `a` is in `A'`.

## Concrete Example

Let's see this in action with a concrete example: three apples and two buckets.

```agda
module ConcreteExample where

  data Apple : Set where
    apple1 apple2 apple3 : Apple

  data Bucket : Set where
    bucket1 bucket2 : Bucket

  placement : Apple → Bucket
  placement apple1 = bucket1
  placement apple2 = bucket1
  placement apple3 = bucket2

  open ApplesAndBucketsTheorem Apple Bucket placement
```

### Scenario: Subset {apple1}

Consider the subset `A' = {apple1}`:

```agda
  AppleSubset : Powerset Apple
  AppleSubset apple1 = ⊤ where
    data ⊤ : Set where
      tt : ⊤
  AppleSubset apple2 = ⊥
  AppleSubset apple3 = ⊥
```

Now let's compute the three images:

**f!(AppleSubset)**: Which buckets contain at least one of `{apple1}`?

- `apple1` is in `bucket1`
- Therefore, `f!(AppleSubset) = {bucket1}`

**f∗(AppleSubset)**: Which buckets contain _only_ apples from `{apple1}`?

- `bucket1` contains `apple1` and `apple2`, but `apple2 ∉ AppleSubset`
- `bucket2` contains `apple3`, but `apple3 ∉ AppleSubset`
- Therefore, `f∗(AppleSubset) = ∅` (empty set)

This illustrates the difference between "at least one" (existential) and "all" (universal) quantification!

## Summary

From a single function `f : A → B`, we derived:

1. **f\*** (pullback): maps bucket-subsets to apple-subsets
2. **f!** (existential image): maps apple-subsets to bucket-subsets ("at least one")
3. **f∗** (universal image): maps apple-subsets to bucket-subsets ("only")

These functors satisfy two adjunctions:

- **f! ⊣ f\***: The existential image is left adjoint to the pullback
- **f\* ⊣ f∗**: The pullback is left adjoint to the universal image

This pattern appears throughout mathematics: functions between sets induce adjoint functors between their powersets!
