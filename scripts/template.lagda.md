---
layout: agda
title: "Title Here"
section: "Definitions"
chapter: 2
number: N
---

# Title Here

## Textbook

**[Definition/Example/Exercise/Proposition] 2.N.** Paste the textbook text here.

## Diagram

```
Draw any diagrams, matrices, tables, or worked examples here.
This helps make the Agda structure obvious.
```

## Agda

```agda
module TYPE.chapter2.Name where

-- Check src/plumbing/ for postulates (reals, classical logic)
-- open import plumbing.Reals using ([0,∞]; 0ℝ; ∞; _≥_; _+ℝ_)

-- Check src/definitions/ before using stdlib
open import definitions.chapter1.Preorder using (Preorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Your formalization here
```
