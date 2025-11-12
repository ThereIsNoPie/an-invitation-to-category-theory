---
layout: agda
title: "Opposite Symmetric Monoidal Preorder"
section: "Propositions"
chapter: 2
number: 22
---

# Opposite Symmetric Monoidal Preorder

## Textbook Definition

**Proposition 2.22.** Suppose X = (X, ≤) is a preorder and X^op = (X, ≥) is its opposite. If (X, ≤, I, ⊗) is a symmetric monoidal preorder then so is its opposite, (X, ≥, I, ⊗).

**Proof.** Let's first check monotonicity. Suppose x₁ ≥ y₁ and x₂ ≥ y₂ in X^op; we need to show that x₁ ⊗ x₂ ≥ y₁ ⊗ y₂. But by definition of opposite order, we have y₁ ≤ x₁ and y₂ ≤ x₂ in X, and thus y₁ ⊗ y₂ ≤ x₁ ⊗ x₂ in X. Thus indeed x₁ ⊗ x₂ ≥ y₁ ⊗ y₂ in X^op.

## Agda Setup

```agda
module propositions.chapter2.OppositeSymmetricMonoidalPreorder where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## The Opposite Preorder

Given a preorder (X, ≤), we construct its opposite (X, ≥).

```agda
-- The opposite preorder: reverse the ordering
op : Preorder → Preorder
op P = record
  { Carrier = Carrier
  ; _≤_ = λ x y → y ≤ x  -- x ≤^op y means y ≤ x
  ; isPreorder = record
      { reflexive = reflexive
      ; transitive = λ y≤x z≤y → transitive z≤y y≤x  -- reversed order
      }
  }
  where open Preorder P
```

## Proposition

If (X, ≤, I, ⊗) is a symmetric monoidal preorder, then so is (X, ≥, I, ⊗).

```agda
opposite-symmetric-monoidal : SymmetricMonoidalPreorder → SymmetricMonoidalPreorder
```

## Proof

**Strategy:** We construct the opposite preorder X^op and show that the monoidal structure (I, ⊗) satisfies the required properties. Monotonicity follows by reversing the order in the original monotonicity proof. The other properties (unitality, associativity, symmetry) are equalities and thus unchanged.

```agda
opposite-symmetric-monoidal SMP = record
  { preorder = op preorder
  ; structure = op-structure
  }
  where
    open SymmetricMonoidalPreorder SMP
    open Preorder preorder renaming (_≤_ to _≤X_)
    open SymmetricMonoidalStructure structure renaming (I to I₀; _⊗_ to _⊗₀_)

    op-structure : SymmetricMonoidalStructure (op preorder)
    op-structure = record
      { I = I₀
      ; _⊗_ = _⊗₀_

      -- (a) Monotonicity in X^op
      -- If x₁ ≥ y₁ and x₂ ≥ y₂ in X^op, then x₁ ⊗ x₂ ≥ y₁ ⊗ y₂ in X^op
      -- By definition: x₁ ≥^op y₁ means y₁ ≤ x₁ in X
      ; monotonicity = λ {x₁} {x₂} {y₁} {y₂} y₁≤x₁ y₂≤x₂ →
          -- We have: y₁ ≤X x₁ and y₂ ≤X x₂ in X
          -- By monotonicity in X: y₁ ⊗₀ y₂ ≤X x₁ ⊗₀ x₂
          -- Therefore: x₁ ⊗₀ x₂ ≥^op y₁ ⊗₀ y₂ in X^op
          SymmetricMonoidalStructure.monotonicity structure y₁≤x₁ y₂≤x₂

      -- (b) Unitality (equalities unchanged)
      ; left-unit = SymmetricMonoidalStructure.left-unit structure
      ; right-unit = SymmetricMonoidalStructure.right-unit structure

      -- (c) Associativity (equality unchanged)
      ; associativity = SymmetricMonoidalStructure.associativity structure

      -- (d) Symmetry (equality unchanged)
      ; symmetry = SymmetricMonoidalStructure.symmetry structure
      }
```

## Interpretation

This proposition shows that the concept of symmetric monoidal preorder is self-dual with respect to order reversal. The monoidal structure (I, ⊗) works the same way whether we use ≤ or ≥, because:

- **Monotonicity adapts:** The order reversal in X^op exactly compensates for reversing the inequality in the monotonicity condition
- **Equalities are preserved:** Unit, associativity, and symmetry laws use equality, not ordering, so they transfer directly

This is why Cost = ([0, ∞], ≥, 0, +) works as a monoidal preorder even though we typically think of real numbers with ≤.
```
