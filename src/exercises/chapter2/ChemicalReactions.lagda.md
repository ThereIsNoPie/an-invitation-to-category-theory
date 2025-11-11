---
layout: agda
title: "Chemical Reactions as Symmetric Monoidal Preorder"
section: "Exercises"
chapter: 2
number: 11
---

# Exercise 2.11: Chemical Reactions

## Textbook Exercise

**Exercise 2.11.** Here is an exercise for people familiar with reaction equations: check that conditions (a), (b), (c), and (d) of Definition 2.1 hold.

**Context:** In high school chemistry, we work with chemical equations, where material collections such as H₂O, NaCl, 2NaOH, CH₄ + 3O₂ are put together in the form of reaction equations, such as:
```text
2H₂O + 2Na → 2NaOH + H₂
```

We can consider reaction equations as taking place inside a single symmetric monoidal preorder (Mat, →, 0, +), where:
- **Mat** is the set of all collections of atoms and molecules (materials)
- **→** is the reaction relation (taking the place of ≤)
- **+** is the operation of combining materials (taking the place of ⊗)
- **0** is the empty collection (the monoidal unit)

## Agda Setup

```agda
module exercises.chapter2.ChemicalReactions where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## Problem

Verify that (Mat, →, 0, +) forms a symmetric monoidal preorder by constructing the required structure.

```agda
module _
  -- Given: a set of all material collections
  (Mat : Set)

  -- Given: the monoidal structure
  (0ₘ : Mat)                        -- The empty material collection (monoidal unit)
  (_+ₘ_ : Mat → Mat → Mat)          -- Combining two material collections (monoidal product)

  -- Given: the reaction relation (x →ₘ y means "x can react to form y")
  (_→ₘ_ : Mat → Mat → Set)

  -- Given: →ₘ forms a preorder
  (→ₘ-refl : ∀ {x : Mat} → x →ₘ x)   -- Reflexivity
  (→ₘ-trans : ∀ {x y z : Mat} → x →ₘ y → y →ₘ z → x →ₘ z)  -- Transitivity

  -- Given: the symmetric monoidal axioms
  -- (a) Monotonicity: reactions can be performed in parallel
  (→ₘ-monotonic : ∀ {x₁ x₂ y₁ y₂ : Mat} →
                  x₁ →ₘ y₁ → x₂ →ₘ y₂ → (x₁ +ₘ x₂) →ₘ (y₁ +ₘ y₂))

  -- (b) Unitality: adding nothing doesn't change the material
  (+ₘ-identityˡ : ∀ {x : Mat} → 0ₘ +ₘ x ≡ x)
  (+ₘ-identityʳ : ∀ {x : Mat} → x +ₘ 0ₘ ≡ x)

  -- (c) Associativity: grouping doesn't matter
  (+ₘ-assoc : ∀ {x y z : Mat} → (x +ₘ y) +ₘ z ≡ x +ₘ (y +ₘ z))

  -- (d) Symmetry: order doesn't matter when combining
  (+ₘ-comm : ∀ {x y : Mat} → x +ₘ y ≡ y +ₘ x)
  where

  private
    -- The preorder structure for materials
    Mat-preorder : Preorder
    Mat-preorder = record
      { Carrier = Mat
      ; _≤_ = _→ₘ_
      ; isPreorder = record
          { reflexive = →ₘ-refl
          ; transitive = →ₘ-trans
          }
      }

  -- The exercise: construct the symmetric monoidal structure
  exercise-2-11 : SymmetricMonoidalStructure Mat-preorder
```

## Solution

**Strategy:** We construct the symmetric monoidal structure by showing that all the given axioms align with Definition 2.1. Each axiom has a clear chemical interpretation:

- **(a) Monotonicity**: If we can perform reaction A and reaction B separately, we can perform both reactions in parallel (in the same beaker).

- **(b) Unitality**: Adding or removing nothing from a material collection leaves it unchanged.

- **(c) Associativity**: Whether we think of "2H₂ + O₂ + catalyst" as "(2H₂ + O₂) + catalyst" or "2H₂ + (O₂ + catalyst)" makes no difference - it's the same collection of materials.

- **(d) Symmetry**: "H₂ + O₂" is the same material collection as "O₂ + H₂" - order doesn't matter when we pour materials together.

```agda
  exercise-2-11 = record
    { I = 0ₘ
    ; _⊗_ = _+ₘ_
    ; monotonicity = →ₘ-monotonic
    ; left-unit = +ₘ-identityˡ
    ; right-unit = +ₘ-identityʳ
    ; associativity = +ₘ-assoc
    ; symmetry = +ₘ-comm
    }

  -- We can also package this as a full symmetric monoidal preorder
  chemical-reactions : SymmetricMonoidalPreorder
  chemical-reactions = record
    { preorder = Mat-preorder
    ; structure = exercise-2-11
    }
```

## Chemical Interpretation

**Reflexivity** (x →ₘ x): Any material can "react" to itself trivially - this represents the do-nothing reaction.

**Transitivity** (x →ₘ y, y →ₘ z implies x →ₘ z): If we can transform x into y, and y into z, we can transform x into z by performing both reactions in sequence.

**Monotonicity**: The key property that makes this a monoidal preorder. If we have two separate reactions we can perform:
```text
x₁ → y₁  and  x₂ → y₂
```
Then we can combine the starting materials and perform both reactions:
```text
x₁ + x₂ → y₁ + y₂
```

For example, if 2H₂ + O₂ → 2H₂O and 2Na + Cl₂ → 2NaCl, then:
```text
(2H₂ + O₂) + (2Na + Cl₂) → 2H₂O + 2NaCl
```

This is the essence of being able to run multiple chemical reactions in parallel.
