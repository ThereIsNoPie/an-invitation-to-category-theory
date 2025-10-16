---
layout: agda
title: "Partition"
section: "Definitions"
chapter: 1
number: 10
---

# Partition

**Definition 1.10.** If A is a set, a *partition of A* consists of a set P and, for each p ∈ P, a nonempty subset A_p ⊆ A, such that

A = ⋃_{p∈P} A_p and if p ≠ q then A_p ∩ A_q = ∅.

We may denote the partition by {A_p}_{p∈P}. We refer to P as the *set of part labels* and if p ∈ P is a part label, we refer to A_p as the *pth part*. The condition says that each element a ∈ A is in exactly one part.

We consider two different partitions {A_p}_{p∈P} and {A'_{p'}}_{p'∈P'} of A to be the same if for each p ∈ P there exists a p' ∈ P' with A_p = A'_{p'}. In other words, if two ways to divide A into parts are exactly the same – the only change is in the labels – then we don't make a distinction between them.

```agda
module definitions.Partition where

open import Data.Product using (_×_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- A subset of a set A
Subset : Set → Set₁
Subset A = A → Set

-- A partition of a set A consists of a set P and for each p ∈ P,
-- a nonempty subset A_p ⊆ A
record Partition (A : Set) : Set₁ where
  field
    -- Set of part labels P
    P : Set

    -- For each p ∈ P, a nonempty subset A_p ⊆ A
    A[_] : P → Subset A

    -- Each part is nonempty
    nonempty : ∀ p → Σ[ a ∈ A ] (A[ p ] a)

    -- A = ⋃_{p∈P} A_p (every element is in some part)
    union : ∀ a → Σ[ p ∈ P ] (A[ p ] a)

    -- If p ≠ q then A_p ∩ A_q = ∅ (parts are disjoint)
    disjoint : ∀ {p q} → ¬ (p ≡ q) → ∀ {a} → ¬ (A[ p ] a × A[ q ] a)
```