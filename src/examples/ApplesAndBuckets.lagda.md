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

From a single function f : Apples → Buckets, we derive three functors and two adjunctions.

```agda
Powerset : Set → Set₁
Powerset X = X → Set

_⊆_ : {X : Set} → Powerset X → Powerset X → Set
_⊆_ S T = ∀ {x} → S x → T x

module ApplesAndBucketsTheorem (Apples Buckets : Set) (f : Apples → Buckets) where
  A = Apples
  B = Buckets
  𝒫A = Powerset A
  𝒫B = Powerset B

  -- Three functors from one function
  f* : 𝒫B → 𝒫A  -- Pullback: "Which apples go in these buckets?"
  f! : 𝒫A → 𝒫B  -- Existential: "Which buckets have ≥1 of these apples?"
  f∗ : 𝒫A → 𝒫B  -- Universal: "Which buckets have only these apples?"

  -- Two adjunctions
  f!⊆→⊆f* : ∀ {A' B'} → f! A' ⊆ B' → A' ⊆ f* B'
  ⊆f*→f!⊆ : ∀ {A' B'} → A' ⊆ f* B' → f! A' ⊆ B'

  f*⊆→⊆f∗ : ∀ {B' A'} → f* B' ⊆ A' → B' ⊆ f∗ A'
  ⊆f∗→f*⊆ : ∀ {B' A'} → B' ⊆ f∗ A' → f* B' ⊆ A'
```

### Implementation

**Strategy:** Use quantifiers (∃ for f!, ∀ for f∗), prove adjunctions directly.

```agda
  -- Pullback: a ∈ f*(B') iff f(a) ∈ B'
  f* B' a = B' (f a)

  -- Existential: b ∈ f!(A') iff ∃a ∈ A'. f(a) = b
  f! A' b = Σ[ a ∈ A ] (A' a × f a ≡ b)

  -- Universal: b ∈ f∗(A') iff ∀a. f(a) = b → a ∈ A'
  f∗ A' b = ∀ {a} → f a ≡ b → A' a

  -- Adjunction 1: f! ⊣ f*
  f!⊆→⊆f* f!A'⊆B' {a} a∈A' = f!A'⊆B' (a , a∈A' , refl)
  ⊆f*→f!⊆ A'⊆f*B' {b} (a , a∈A' , refl) = A'⊆f*B' a∈A'

  -- Adjunction 2: f* ⊣ f∗
  f*⊆→⊆f∗ f*B'⊆A' {b} b∈B' {a} refl = f*B'⊆A' b∈B'
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

One function f : A → B induces:
- Three functors: f* (pullback), f! (existential), f∗ (universal)
- Two adjunctions: f! ⊣ f* and f* ⊣ f∗

This pattern appears throughout mathematics!
