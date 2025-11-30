---
layout: agda
title: "V-Category"
section: "Definitions"
chapter: 2
number: 30
---

# V-Category

## Textbook Definition

**Definition 2.30.** Let V = (V, ≤, I, ⊗) be a symmetric monoidal preorder. A V-category X consists of two constituents, satisfying two properties. To specify X,

(i) one specifies a set Ob(X), elements of which are called objects;

(ii) for every two objects x, y, one specifies an element X(x, y) ∈ V, called the hom-object.

The above constituents are required to satisfy two properties:

(a) for every object x ∈ Ob(X) we have I ≤ X(x, x),

(b) for every three objects x, y, z ∈ Ob(X), we have X(x, y) ⊗ X(y, z) ≤ X(x, z).

We call V the base of the enrichment for X or say that X is enriched in V.

## Agda Formalization

```agda
module definitions.chapter2.VCategory where

open import definitions.chapter2.SymmetricMonoidalPreorder using (SymmetricMonoidalPreorder)

-- A V-category X is enriched in a symmetric monoidal preorder V
record VCategory (V : SymmetricMonoidalPreorder) : Set₁ where
  open SymmetricMonoidalPreorder V

  field
    -- (i) A set Ob(X) of objects
    Ob : Set

    -- (ii) For every two objects x, y, a hom-object X(x, y) ∈ V
    hom : Ob → Ob → Carrier

    -- (a) Identity: I ≤ X(x, x)
    identity : ∀ {x} → I ≤ hom x x

    -- (b) Composition: X(x, y) ⊗ X(y, z) ≤ X(x, z)
    composition : ∀ {x y z} → (hom x y ⊗ hom y z) ≤ hom x z
```