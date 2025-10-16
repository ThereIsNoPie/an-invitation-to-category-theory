---
layout: agda
title: "Relation"
section: "Definitions"
chapter: 1
number: 8
---

# Relation

**Definition 1.8.** Let X and Y be sets. A *relation between X and Y* is a subset R ⊆ X × Y. A *binary relation on X* is a relation between X and X, i.e. a subset R ⊆ X × X.

```agda
module definitions.Relation where

open import Data.Product using (_×_)

-- A relation between two sets X and Y is a subset R ⊆ X × Y
-- In type theory, this is represented as a binary predicate
Rel : Set → Set → Set₁
Rel A B = A → B → Set

-- A binary relation on a set X is a relation between X and X
-- i.e., a subset R ⊆ X × X
BinRel : Set → Set₁
BinRel A = Rel A A
```