---
layout: agda
title: "Commutative Monoid as Symmetric Monoidal Preorder"
section: "Examples"
chapter: 2
number: 5
---

# Example 2.5: Commutative Monoid as Symmetric Monoidal Preorder

## Textbook Description

**Example 2.5.** A *monoid* consists of a set M, a function ∗ : M × M → M called the monoid multiplication, and an element e ∈ M called the monoid unit, such that, when you write ∗(m, n) as m ∗ n, i.e. using infix notation, the equations

m ∗ e = m,    e ∗ m = m,    (m ∗ n) ∗ p = m ∗ (n ∗ p)    (2.2)

hold for all m, n, p ∈ M. It is called *commutative* if also m ∗ n = n ∗ m.

Every set S determines a *discrete preorder* Disc_S (where m ≤ n iff m = n; see Example 1.27), and it is easy to check that if (M, e, ∗) is a commutative monoid then (Disc_M, =, e, ∗) is a symmetric monoidal preorder.

## Agda Setup

```agda
module examples.chapter2.CommutativeMonoidAsSymmetricMonoidalPreorder where

open import definitions.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
```

## The Example

Every commutative monoid induces a symmetric monoidal preorder via the discrete ordering.

```agda
-- The discrete preorder on a set: x ≤ y iff x ≡ y
module DiscretePreorder (A : Set) where

  Disc : Preorder
  Disc = record
    { Carrier = A
    ; _≤_ = _≡_
    ; isPreorder = record
        { reflexive = refl
        ; transitive = trans
        }
    }

-- A commutative monoid (simplified definition following textbook)
record CommutativeMonoid : Set₁ where
  field
    Carrier : Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier

    -- Monoid laws (2.2)
    right-identity : ∀ {m} → m ∙ ε ≡ m
    left-identity : ∀ {m} → ε ∙ m ≡ m
    associativity : ∀ {m n p} → (m ∙ n) ∙ p ≡ m ∙ (n ∙ p)

    -- Commutativity
    commutativity : ∀ {m n} → m ∙ n ≡ n ∙ m

-- Main construction: commutative monoid → symmetric monoidal preorder
commutative-monoid→symmetric-monoidal-preorder :
  CommutativeMonoid → SymmetricMonoidalPreorder
```

### Implementation

**Strategy:** The discrete preorder has x ≤ y iff x ≡ y. We verify that the monoid operation preserves this ordering (which is trivial since we can use congruence).

```agda
commutative-monoid→symmetric-monoidal-preorder M = record
  { preorder = Disc
  ; structure = monoidal-structure
  }
  where
    open CommutativeMonoid M
    open DiscretePreorder Carrier

    monoidal-structure : SymmetricMonoidalStructure Disc
    monoidal-structure = record
      { I = ε
      ; _⊗_ = _∙_

      -- (a) Monotonicity: if x₁ ≡ y₁ and x₂ ≡ y₂, then x₁ ∙ x₂ ≡ y₁ ∙ y₂
      ; monotonicity = λ {x₁} {x₂} {y₁} {y₂} x₁≡y₁ x₂≡y₂ → cong₂ _∙_ x₁≡y₁ x₂≡y₂

      -- (b) Unitality
      ; left-unit = left-identity
      ; right-unit = right-identity

      -- (c) Associativity
      ; associativity = associativity

      -- (d) Symmetry (commutativity)
      ; symmetry = commutativity
      }
```

## Concrete Example: Natural Numbers with Addition

The natural numbers with addition form a commutative monoid.

```agda
open import Data.Nat using (ℕ; _+_; zero)
open import Data.Nat.Properties using (+-identityʳ; +-identityˡ; +-assoc; +-comm)

ℕ-commutative-monoid : CommutativeMonoid
ℕ-commutative-monoid = record
  { Carrier = ℕ
  ; _∙_ = _+_
  ; ε = zero
  ; right-identity = λ {m} → +-identityʳ m
  ; left-identity = λ {m} → +-identityˡ m
  ; associativity = λ {m} {n} {p} → +-assoc m n p
  ; commutativity = λ {m} {n} → +-comm m n
  }

-- This gives us (Disc_ℕ, =, 0, +) as a symmetric monoidal preorder
ℕ+-symmetric-monoidal : SymmetricMonoidalPreorder
ℕ+-symmetric-monoidal = commutative-monoid→symmetric-monoidal-preorder ℕ-commutative-monoid
```

## Note

The discrete preorder Disc_M has the property that x ≤ y if and only if x = y. This means:

- **Monotonicity** is automatic: if x₁ = y₁ and x₂ = y₂, then clearly x₁ ∗ x₂ = y₁ ∗ y₂ by substitution
- **Other properties** transfer directly from the monoid laws

This example shows that symmetric monoidal preorders generalize commutative monoids.
```
