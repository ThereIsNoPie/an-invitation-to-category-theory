---
layout: agda
title: "Quantale"
section: "Definitions"
chapter: 2
number: 66
---

# Quantale

## Textbook Definition

**Definition 2.62.** A *unital commutative quantale* is a symmetric monoidal closed preorder $\mathcal{V} = (V, \leq, I, \otimes, \multimap)$ that has all joins: $\bigvee A$ exists for every $A \subseteq V$. In particular, we often denote the empty join by $0 := \bigvee \varnothing$.

## Agda Setup

```agda
module definitions.chapter2.Quantale where

open import definitions.chapter2.MonoidalClosed
  using (MonoidalClosedPreorder; IsMonoidalClosed)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Level using (Level; _⊔_)
```

## All Joins

A preorder has all joins if every subset has a join. We model this using an indexed join over any index set.

```agda
-- A preorder has all joins if for every index set I and family A : I → V,
-- the join ⋁ᵢ A(i) exists
record HasAllJoins (V : SymmetricMonoidalPreorder) : Set₁ where
  open SymmetricMonoidalPreorder V

  field
    -- The join operation, indexed by any set
    ⋁ : {I : Set} → (I → Carrier) → Carrier

    -- Join is an upper bound: a(i) ≤ ⋁ a for all i
    join-ub : ∀ {I : Set} {a : I → Carrier} {i : I} → a i ≤ ⋁ a

    -- Join is the least upper bound: if b is an upper bound, then ⋁ a ≤ b
    join-lub : ∀ {I : Set} {a : I → Carrier} {b : Carrier}
             → (∀ i → a i ≤ b) → ⋁ a ≤ b

  -- The empty join (indexed by the empty type)
  open import Data.Empty using (⊥)

  𝟘 : Carrier
  𝟘 = ⋁ {I = ⊥} (λ ())

  -- Binary join
  open import Data.Bool using (Bool; true; false)

  _∨_ : Carrier → Carrier → Carrier
  x ∨ y = ⋁ {I = Bool} (λ { true → x ; false → y })
```

## Agda Formalization

```agda
-- A unital commutative quantale
record Quantale : Set₁ where
  field
    closedPreorder : MonoidalClosedPreorder
    hasAllJoins : HasAllJoins (MonoidalClosedPreorder.base closedPreorder)

  open MonoidalClosedPreorder closedPreorder public
  open HasAllJoins hasAllJoins public
```

## Properties

From Proposition 2.61(b), we know that the monoidal product distributes over joins in a quantale.

```agda
module QuantaleProperties (Q : Quantale) where
  open Quantale Q

  -- The monoidal product distributes over joins (follows from the adjunction)
  -- v ⊗ (⋁ᵢ aᵢ) ≅ ⋁ᵢ (v ⊗ aᵢ)
  -- This is because (-⊗v) is a left adjoint, and left adjoints preserve joins
  postulate
    ⊗-distributes-⋁ : ∀ {I : Set} {a : I → Carrier} {v : Carrier}
                    → (v ⊗ ⋁ a) ≤ ⋁ (λ i → v ⊗ a i)
```

## Interpretation

A quantale is a monoidal closed preorder with "enough joins" to perform operations like matrix multiplication. The key examples are:

- **Bool**: has all joins (∨ is boolean OR, the empty join is false)
- **Cost**: has all joins (∨ is infimum/min, the empty join is ∞)

The distributivity of ⊗ over joins is crucial for matrix multiplication to work correctly.
