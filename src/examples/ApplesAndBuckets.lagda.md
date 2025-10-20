---
layout: agda
title: "Apples and Buckets"
section: "Examples"
chapter: 1
number: 109
---

# Example 1.109: Apples and Buckets

## Textbook Description

**Example 1.109 (Apples and Buckets).** This example demonstrates a beautiful phenomenon in category theory: **a single function induces three different adjoint functors**. We'll use the intuitive metaphor of placing apples into buckets to understand these abstract concepts.

Imagine we have a collection of apples and a collection of buckets, and each apple is placed in exactly one bucket. This placement is represented by a function `f : Apples → Buckets`.

Now, we can ask questions about _subsets_ of apples and subsets of buckets. Given a subset of apples, which buckets are relevant? Given a subset of buckets, which apples are relevant? These questions lead to three different functors between powersets.

## Agda Setup

```agda
module examples.ApplesAndBuckets where

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_)
```

## The Example

Given a function `f : Apples → Buckets`, we derive three functors between powersets that form two adjoint pairs.

### Key Type Definitions

We represent subsets using the **powerset** construction. A subset of `X` is represented as a predicate `X → Set`.

```agda
Powerset : Set → Set₁
Powerset X = X → Set

-- Subset inclusion
_⊆_ : {X : Set} → Powerset X → Powerset X → Set
_⊆_ S T = ∀ {x} → S x → T x
```

### The Three Functors

```agda
module ApplesAndBucketsTheorem (Apples Buckets : Set) (f : Apples → Buckets) where

  A = Apples
  B = Buckets
  𝒫A = Powerset A
  𝒫B = Powerset B

  -- Functor 1: Pullback f* : 𝒫B → 𝒫A
  -- "Which apples go into these buckets?"
  f* : 𝒫B → 𝒫A

  -- Functor 2: Existential Image f! : 𝒫A → 𝒫B
  -- "Which buckets contain at least one of these apples?"
  f! : 𝒫A → 𝒫B

  -- Functor 3: Universal Image f∗ : 𝒫A → 𝒫B
  -- "Which buckets contain only these apples?"
  f∗ : 𝒫A → 𝒫B
```

### Implementation

**Strategy:** Define each functor based on its intuitive meaning.

```agda
  -- Pullback: f*(B') = { a ∈ A | f(a) ∈ B' }
  -- An apple a is in f*(B') if its bucket f(a) is in B'
  f* B' a = B' (f a)

  -- Existential Image: f!(A') = { b ∈ B | ∃a ∈ A'. f(a) = b }
  -- A bucket b is in f!(A') if there exists some apple a in A' such that f(a) = b
  f! A' b = Σ[ a ∈ A ] (A' a × f a ≡ b)

  -- Universal Image: f∗(A') = { b ∈ B | ∀a. f(a) = b → a ∈ A' }
  -- A bucket b is in f∗(A') if every apple that goes into b is in A'
  f∗ A' b = ∀ {a} → f a ≡ b → A' a
```

## The Two Adjunctions

```agda
  -- Adjunction 1: f! ⊣ f*
  -- f!(A') ⊆ B' ⟺ A' ⊆ f*(B')
  f!⊆→⊆f* : ∀ {A' B'} → f! A' ⊆ B' → A' ⊆ f* B'
  ⊆f*→f!⊆ : ∀ {A' B'} → A' ⊆ f* B' → f! A' ⊆ B'

  -- Adjunction 2: f* ⊣ f∗
  -- f*(B') ⊆ A' ⟺ B' ⊆ f∗(A')
  f*⊆→⊆f∗ : ∀ {B' A'} → f* B' ⊆ A' → B' ⊆ f∗ A'
  ⊆f∗→f*⊆ : ∀ {B' A'} → B' ⊆ f∗ A' → f* B' ⊆ A'
```

### Implementation

**Strategy:** Prove the adjunction properties using the functor definitions directly.

```agda
  -- Adjunction 1 proofs

  -- Forward: If all buckets containing apples from A' are in B',
  --          then all apples in A' map to buckets in B'
  f!⊆→⊆f* f!A'⊆B' {a} a∈A' = f!A'⊆B' (a , a∈A' , refl)

  -- Backward: If all apples in A' map to buckets in B',
  --           then all buckets containing an apple from A' are in B'
  ⊆f*→f!⊆ A'⊆f*B' {b} (a , a∈A' , refl) = A'⊆f*B' a∈A'

  -- Adjunction 2 proofs

  -- Forward: If all apples in buckets B' are in A',
  --          then every bucket in B' contains only apples from A'
  f*⊆→⊆f∗ f*B'⊆A' {b} b∈B' {a} refl = f*B'⊆A' b∈B'

  -- Backward: If every bucket in B' contains only apples from A',
  --           then all apples in buckets B' are in A'
  ⊆f∗→f*⊆ B'⊆f∗A' {a} fa∈B' = B'⊆f∗A' fa∈B' refl
```

## Concrete Example

Let's see this in action with three apples and two buckets.

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

1. **f*** (pullback): maps bucket-subsets to apple-subsets
2. **f!** (existential image): maps apple-subsets to bucket-subsets ("at least one")
3. **f∗** (universal image): maps apple-subsets to bucket-subsets ("only")

These functors satisfy two adjunctions:

- **f! ⊣ f***: The existential image is left adjoint to the pullback
- **f* ⊣ f∗**: The pullback is left adjoint to the universal image

This pattern appears throughout mathematics: functions between sets induce adjoint functors between their powersets!
```
