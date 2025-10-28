---
layout: agda
title: "Symmetric Monoidal Preorder"
section: "Definitions"
chapter: 2
number: 1
---

# Symmetric Monoidal Preorder

## Textbook Definition

**Definition 2.1.** A *(strict) symmetric monoidal structure* on a preorder (X, ≤) consists of two constituents:

(i) an element I ∈ X, called the *monoidal unit*,

(ii) a function ⊗ : X × X → X, called the *monoidal product*.

These constituents must satisfy the following properties, where we write ⊗(x₁, x₂) = x₁ ⊗ x₂:

(a) for all x₁, x₂, y₁, y₂ ∈ X, if x₁ ≤ y₁ and x₂ ≤ y₂, then x₁ ⊗ x₂ ≤ y₁ ⊗ y₂,

(b) for all x ∈ X, the equations I ⊗ x = x and x ⊗ I = x hold,

(c) for all x, y, z ∈ X, the equation (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z) holds,

(d) for all x, y ∈ X, the equation x ⊗ y = y ⊗ x holds.

We call these conditions *monotonicity*, *unitality*, *associativity*, and *symmetry* respectively. A preorder equipped with a symmetric monoidal structure, (X, ≤, I, ⊗), is called a *symmetric monoidal preorder*.

## Agda Formalization

```agda
module definitions.chapter2.SymmetricMonoidalPreorder where

open import definitions.chapter1.Preorder using (Preorder)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- A symmetric monoidal structure on a preorder (X, ≤)
record SymmetricMonoidalStructure (P : Preorder) : Set where
  open Preorder P

  field
    -- (i) Monoidal unit
    I : Carrier

    -- (ii) Monoidal product
    _⊗_ : Carrier → Carrier → Carrier

    -- (a) Monotonicity: if x₁ ≤ y₁ and x₂ ≤ y₂, then x₁ ⊗ x₂ ≤ y₁ ⊗ y₂
    monotonicity : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ y₁ → x₂ ≤ y₂ → (x₁ ⊗ x₂) ≤ (y₁ ⊗ y₂)

    -- (b) Unitality: I ⊗ x = x and x ⊗ I = x
    left-unit  : ∀ {x} → I ⊗ x ≡ x
    right-unit : ∀ {x} → x ⊗ I ≡ x

    -- (c) Associativity: (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)
    associativity : ∀ {x y z} → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)

    -- (d) Symmetry: x ⊗ y = y ⊗ x
    symmetry : ∀ {x y} → x ⊗ y ≡ y ⊗ x

-- A symmetric monoidal preorder is a preorder equipped with
-- a symmetric monoidal structure (X, ≤, I, ⊗)
record SymmetricMonoidalPreorder : Set₁ where
  field
    preorder : Preorder
    structure : SymmetricMonoidalStructure preorder

  open Preorder preorder public
  open SymmetricMonoidalStructure structure public
```
