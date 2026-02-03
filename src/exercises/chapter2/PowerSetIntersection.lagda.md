---
layout: agda
title: "Power Set with Intersection"
section: "Exercises"
chapter: 2
number: 19
---

# Exercise 2.19: Power Set with Intersection

## Textbook Exercise

**Exercise 2.19.** Let S be a set and let P(S) be its power set, the set of all subsets of S, including the empty subset, ∅ ⊆ S, and the "everything" subset, S ⊆ S. We can give P(S) an order: A ≤ B is given by the subset relation A ⊆ B, as discussed in Example 1.45. We propose a symmetric monoidal structure on P(S) with monoidal unit S and monoidal product given by intersection A ∩ B.

Does it satisfy the conditions of Definition 2.1?

## Agda Setup

```agda
module exercises.chapter2.PowerSetIntersection where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_; suc)
open import Relation.Unary using (Pred; _∈_; _⊆_; ∅; U)
open import Data.Unit using (⊤; tt)

-- We need a leveled version of funext for PowerSet
postulate
  funextₗ : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
            (∀ x → f x ≡ g x) → f ≡ g
  propextₗ : {ℓ : Level} {P Q : Set ℓ} → (P → Q) → (Q → P) → P ≡ Q

-- Leveled versions of preorder structures for working with PowerSet
-- (which lives in Set₁ instead of Set)

record IsPreorderₗ {c ℓ : Level} {A : Set c} (_≤_ : A → A → Set ℓ) : Set (c ⊔ ℓ) where
  field
    reflexive  : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

record Preorderₗ (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where
  field
    Carrier    : Set c
    _≤_        : Carrier → Carrier → Set ℓ
    isPreorder : IsPreorderₗ _≤_

  open IsPreorderₗ isPreorder public

record SymmetricMonoidalStructureₗ {c ℓ : Level} (P : Preorderₗ c ℓ) : Set (c ⊔ ℓ) where
  open Preorderₗ P

  field
    I : Carrier
    _⊗_ : Carrier → Carrier → Carrier

    monotonicity : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤ y₁ → x₂ ≤ y₂ → (x₁ ⊗ x₂) ≤ (y₁ ⊗ y₂)
    left-unit  : ∀ {x} → I ⊗ x ≡ x
    right-unit : ∀ {x} → x ⊗ I ≡ x
    associativity : ∀ {x y z} → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    symmetry : ∀ {x y} → x ⊗ y ≡ y ⊗ x

record SymmetricMonoidalPreorderₗ (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where
  field
    preorder : Preorderₗ c ℓ
    structure : SymmetricMonoidalStructureₗ preorder

  open Preorderₗ preorder public
  open SymmetricMonoidalStructureₗ structure public
```

## Problem

Determine whether (P(S), ⊆, S, ∩) forms a symmetric monoidal preorder.

```agda
-- Power set: predicates on S (characteristic functions)
-- Following the convention used throughout the codebase
PowerSet : Set → Set₁
PowerSet S = S → Set

-- Subset relation for powersets
_⊆'_ : {S : Set} → PowerSet S → PowerSet S → Set
A ⊆' B = ∀ {x} → A x → B x

-- Set intersection
_∩_ : {S : Set} → PowerSet S → PowerSet S → PowerSet S
(A ∩ B) x = A x × B x

-- The full set S (the always-true predicate)
FullSet : {S : Set} → PowerSet S
FullSet x = ⊤

-- The preorder structure on P(S) using leveled version
PowerSet-preorder : (S : Set) → Preorderₗ (suc Level.zero) Level.zero
PowerSet-preorder S = record
  { Carrier = PowerSet S
  ; _≤_ = _⊆'_
  ; isPreorder = record
      { reflexive = λ {A} x∈A → x∈A
      ; transitive = λ {A} {B} {C} A⊆B B⊆C x∈A → B⊆C (A⊆B x∈A)
      }
  }

-- The exercise: construct the symmetric monoidal structure
exercise-2-19 : (S : Set) → SymmetricMonoidalStructureₗ (PowerSet-preorder S)
```

## Solution

**Strategy:** We verify each of the four conditions from Definition 2.1:

- **(a) Monotonicity**: If A₁ ⊆ B₁ and A₂ ⊆ B₂, then A₁ ∩ A₂ ⊆ B₁ ∩ B₂
- **(b) Unitality**: S ∩ A = A and A ∩ S = A
- **(c) Associativity**: (A ∩ B) ∩ C = A ∩ (B ∩ C)
- **(d) Symmetry**: A ∩ B = B ∩ A

All four conditions hold for set intersection with the full set as unit.

```agda
exercise-2-19 S = record
  { I = FullSet
  ; _⊗_ = _∩_
  ; monotonicity = ∩-monotonic
  ; left-unit = ∩-identityˡ
  ; right-unit = ∩-identityʳ
  ; associativity = ∩-assoc
  ; symmetry = ∩-comm
  }
  where
    -- (a) Monotonicity: intersection preserves subset ordering
    ∩-monotonic : ∀ {A₁ A₂ B₁ B₂ : PowerSet S} →
                  A₁ ⊆' B₁ → A₂ ⊆' B₂ → (A₁ ∩ A₂) ⊆' (B₁ ∩ B₂)
    ∩-monotonic A₁⊆B₁ A₂⊆B₂ (x∈A₁ , x∈A₂) = A₁⊆B₁ x∈A₁ , A₂⊆B₂ x∈A₂

    -- (b) Unitality: S is the identity for intersection
    -- We need functional extensionality and propositional extensionality
    ∩-identityˡ : ∀ {A : PowerSet S} → (FullSet ∩ A) ≡ A
    ∩-identityˡ {A} = funextₗ λ x → propextₗ
      (λ where (tt , x∈A) → x∈A)
      (λ x∈A → tt , x∈A)

    ∩-identityʳ : ∀ {A : PowerSet S} → (A ∩ FullSet) ≡ A
    ∩-identityʳ {A} = funextₗ λ x → propextₗ
      (λ where (x∈A , tt) → x∈A)
      (λ x∈A → x∈A , tt)

    -- (c) Associativity: intersection is associative
    ∩-assoc : ∀ {A B C : PowerSet S} → ((A ∩ B) ∩ C) ≡ (A ∩ (B ∩ C))
    ∩-assoc {A} {B} {C} = funextₗ λ x → propextₗ
      (λ where ((x∈A , x∈B) , x∈C) → x∈A , (x∈B , x∈C))
      (λ where (x∈A , (x∈B , x∈C)) → (x∈A , x∈B) , x∈C)

    -- (d) Symmetry: intersection is commutative
    ∩-comm : ∀ {A B : PowerSet S} → (A ∩ B) ≡ (B ∩ A)
    ∩-comm {A} {B} = funextₗ λ x → propextₗ
      (λ where (x∈A , x∈B) → x∈B , x∈A)
      (λ where (x∈B , x∈A) → x∈A , x∈B)

-- Package as a full symmetric monoidal preorder using leveled version
PowerSetIntersection : (S : Set) → SymmetricMonoidalPreorderₗ (suc Level.zero) Level.zero
PowerSetIntersection S = record
  { preorder = PowerSet-preorder S
  ; structure = exercise-2-19 S
  }
```