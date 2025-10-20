---
layout: agda
title: "Quotient"
section: "Definitions"
chapter: 1
number: 16
---

# Quotient

**Definition 1.16.** Given a set A and an equivalence relation ∼ on A, we say that the *quotient A/∼ of A under ∼* is the set of parts of the corresponding partition.

```agda
module definitions.Quotient where

open import definitions.EquivalenceRelation using (IsEquivalence)
open import definitions.Partition using (Partition; Subset)

-- The quotient A/∼ is the set of parts of the partition corresponding to ∼
-- Each part is an equivalence class
--
-- Note: This is the predicative definition (living in Set₁).
-- For computational purposes (e.g., Proposition 1.14), we use the impredicative
-- quotient type from plumbing.ClassicalPostulates, which provides A / _∼_ : Set
-- along with operations [_], quotient-sound, quotient-effective, and quotient-surjective.
Quotient : (A : Set) → (A → A → Set) → Set₁
Quotient A _∼_ = Subset A
```
