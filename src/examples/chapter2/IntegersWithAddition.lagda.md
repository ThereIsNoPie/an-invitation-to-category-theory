---
layout: agda
title: "Integers with Addition"
section: "Examples"
chapter: 2
number: 3
---

# Example 2.3: Integers with Addition

## Textbook Description

**Example 2.3.** There is a well-known preorder structure, denoted ≤, on the set ℝ of real numbers; e.g. −5 ≤ √2. We propose 0 as a monoidal unit and + : ℝ × ℝ → ℝ as a monoidal product. Does (ℝ, ≤, 0, +) satisfy the conditions of Definition 2.1?

If x₁ ≤ y₁ and x₂ ≤ y₂, it is true that x₁ + x₂ ≤ y₁ + y₂. It is also true that 0 + x = x and x + 0 = x, that (x + y) + z = x + (y + z), and that x + y = y + x. Thus (ℝ, ≤, 0, +) satisfies the conditions of being a symmetric monoidal preorder.

**Note:** We formalize this using integers (ℤ) instead of real numbers (ℝ), as the standard library provides integers with all necessary properties.

## Agda Setup

```agda
module examples.chapter2.IntegersWithAddition where

open import definitions.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import Data.Integer using (ℤ; _+_; _≤_; 0ℤ)
open import Data.Integer.Properties using
  ( ≤-refl; ≤-trans; +-mono-≤
  ; +-identityˡ; +-identityʳ
  ; +-assoc; +-comm
  )
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## The Example

We construct (ℤ, ≤, 0, +) as a symmetric monoidal preorder.

```agda
ℤ-preorder : Preorder
ℤ-monoidal-structure : SymmetricMonoidalStructure ℤ-preorder
ℤ-symmetric-monoidal : SymmetricMonoidalPreorder
```

### Implementation

**Strategy:** Verify each condition of Definition 2.1 using properties from Data.Integer.Properties.

```agda
-- First, ℤ with ≤ forms a preorder
ℤ-preorder = record
  { Carrier = ℤ
  ; _≤_ = _≤_
  ; isPreorder = record
      { reflexive = ≤-refl
      ; transitive = ≤-trans
      }
  }

-- The symmetric monoidal structure (0, +) on ℤ
ℤ-monoidal-structure = record
  { I = 0ℤ
  ; _⊗_ = _+_
  ; monotonicity = +-mono-≤
  ; left-unit = λ {x} → +-identityˡ x
  ; right-unit = λ {x} → +-identityʳ x
  ; associativity = λ {x} {y} {z} → +-assoc x y z
  ; symmetry = λ {x} {y} → +-comm x y
  }

-- Combining them: (ℤ, ≤, 0, +) is a symmetric monoidal preorder
ℤ-symmetric-monoidal = record
  { preorder = ℤ-preorder
  ; structure = ℤ-monoidal-structure
  }
```

## Verification

Let's verify each condition explicitly:

**(a) Monotonicity:** If x₁ ≤ y₁ and x₂ ≤ y₂, then x₁ + x₂ ≤ y₁ + y₂. ✓

This is the fundamental property that addition preserves order.

**(b) Unitality:** 0 + x = x and x + 0 = x. ✓

Zero is the additive identity.

**(c) Associativity:** (x + y) + z = x + (y + z). ✓

Addition is associative.

**(d) Symmetry:** x + y = y + x. ✓

Addition is commutative.

Therefore, (ℤ, ≤, 0, +) is indeed a symmetric monoidal preorder (and the same holds for ℝ).
```