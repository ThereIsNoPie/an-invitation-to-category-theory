---
layout: agda
title: "Equivalence Relation"
section: "Definitions"
chapter: 1
number: 13
---

# Equivalence Relation

**Definition 1.13.** Let A be a set. An *equivalence relation on A* is a binary relation, let's give it infix notation ∼, satisfying the following three properties:

(a) a ∼ a, for all a ∈ A,

(b) a ∼ b iff b ∼ a, for all a, b ∈ A,

(c) if a ∼ b and b ∼ c then a ∼ c, for all a, b, c ∈ A.

These properties are called *reflexivity*, *symmetry*, and *transitivity*, respectively.

```agda
module definitions.chapter1.EquivalenceRelation where

open import definitions.chapter1.Relation using (BinRel)

-- An equivalence relation on A is a binary relation satisfying
-- reflexivity, symmetry, and transitivity
record IsEquivalence {A : Set} (_∼_ : BinRel A) : Set where
  field
    -- (a) Reflexivity: a ∼ a for all a ∈ A
    reflexive : ∀ {a} → a ∼ a

    -- (b) Symmetry: a ∼ b iff b ∼ a for all a, b ∈ A
    symmetric : ∀ {a b} → a ∼ b → b ∼ a

    -- (c) Transitivity: if a ∼ b and b ∼ c then a ∼ c
    transitive : ∀ {a b c} → a ∼ b → b ∼ c → a ∼ c
```