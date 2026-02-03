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

Use LaTeX for math: $d(x, y) := |y - x|$ for inline, or display:

$$d(x, y) + d(y, z) \geq d(x, z)$$

## Diagram

```
Draw any diagrams, matrices, tables as ASCII.
This helps make the Agda structure obvious.
```

## Agda

```agda
module TYPE.chapter2.Name where

-- Check src/plumbing/ for postulates (reals, classical logic)
-- Check src/definitions/ before using stdlib
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Your formalization here
```
