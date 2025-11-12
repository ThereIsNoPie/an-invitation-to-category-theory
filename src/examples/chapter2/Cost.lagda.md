---
layout: agda
title: "Lawvere's Monoidal Preorder (Cost)"
section: "Examples"
chapter: 2
number: 21
---

# Example 2.21: Lawvere's Monoidal Preorder (Cost)

## Textbook Description

**Example 2.21 (Lawvere's monoidal preorder, Cost).** Let [0, ∞] denote the set of nonnegative real numbers – such as 0, 1, 15.333, and 2π – together with ∞. Consider the preorder ([0, ∞], ≥), with the usual notion of ≥, where of course ∞ ≥ x for all x ∈ [0, ∞].

There is a monoidal structure on this preorder, where the monoidal unit is 0 and the monoidal product is +. In particular, x + ∞ = ∞ for any x ∈ [0, ∞]. Let's call this monoidal preorder

Cost := ([0, ∞], ≥, 0, +),

because we can think of the elements of [0, ∞] as costs. In terms of structuring "getting from here to there," Cost seems to say "getting from a to b is a question of cost."

The monoidal unit being 0 will translate into saying that you can always get from a to a at no cost. The monoidal product being + will translate into saying that the cost of getting from a to c is at most the cost of getting from a to b plus the cost of getting from b to c. Finally, the "at most" in the previous sentence comes from the ≥.

**Note:** We postulate the nonnegative extended reals [0, ∞] with their necessary properties rather than constructing them explicitly, keeping the formalization simple and close to the textbook presentation.

## Agda Setup

```agda
module examples.chapter2.Cost where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## The Example

NOTE: the Real numbers kinda suck to formalize in Agda. So we postulate pretty much everything making this example a mostly useless addition to the textbook.

We construct Cost = ([0, ∞], ≥, 0, +) as a symmetric monoidal preorder.

```agda
-- Postulate the carrier: nonnegative extended reals [0, ∞]
postulate
  [0,∞] : Set

  -- Distinguished elements
  0ℝ : [0,∞]   -- Zero
  ∞  : [0,∞]   -- Infinity

  -- The ordering ≥ (note: reversed from usual ≤)
  _≥_ : [0,∞] → [0,∞] → Set

  -- Addition on extended nonnegative reals
  _+ℝ_ : [0,∞] → [0,∞] → [0,∞]

  -- Preorder properties
  ≥-refl : ∀ {x : [0,∞]} → x ≥ x
  ≥-trans : ∀ {x y z : [0,∞]} → x ≥ y → y ≥ z → x ≥ z

  -- Infinity is greatest
  ∞-greatest : ∀ {x : [0,∞]} → ∞ ≥ x

  -- Addition properties
  +ℝ-identityˡ : ∀ {x : [0,∞]} → 0ℝ +ℝ x ≡ x
  +ℝ-identityʳ : ∀ {x : [0,∞]} → x +ℝ 0ℝ ≡ x
  +ℝ-assoc : ∀ {x y z : [0,∞]} → (x +ℝ y) +ℝ z ≡ x +ℝ (y +ℝ z)
  +ℝ-comm : ∀ {x y : [0,∞]} → x +ℝ y ≡ y +ℝ x

  -- Monotonicity: if x₁ ≥ y₁ and x₂ ≥ y₂, then x₁ + x₂ ≥ y₁ + y₂
  +ℝ-mono : ∀ {x₁ x₂ y₁ y₂ : [0,∞]} → x₁ ≥ y₁ → x₂ ≥ y₂ → (x₁ +ℝ x₂) ≥ (y₁ +ℝ y₂)

  -- Infinity absorbs addition: x + ∞ = ∞ and ∞ + x = ∞
  +ℝ-∞ʳ : ∀ {x : [0,∞]} → x +ℝ ∞ ≡ ∞
  +ℝ-∞ˡ : ∀ {x : [0,∞]} → ∞ +ℝ x ≡ ∞

-- The Cost symmetric monoidal preorder
Cost-preorder : Preorder
Cost-monoidal-structure : SymmetricMonoidalStructure Cost-preorder
Cost : SymmetricMonoidalPreorder
```

### Implementation

**Strategy:** We postulate the nonnegative extended reals [0, ∞] with their properties, then assemble them into a symmetric monoidal preorder.

```agda
-- [0, ∞] with ≥ forms a preorder
Cost-preorder = record
  { Carrier = [0,∞]
  ; _≤_ = _≥_
  ; isPreorder = record
      { reflexive = ≥-refl
      ; transitive = ≥-trans
      }
  }

-- The symmetric monoidal structure (0, +) on [0, ∞]
Cost-monoidal-structure = record
  { I = 0ℝ
  ; _⊗_ = _+ℝ_
  ; monotonicity = +ℝ-mono
  ; left-unit = +ℝ-identityˡ
  ; right-unit = +ℝ-identityʳ
  ; associativity = +ℝ-assoc
  ; symmetry = +ℝ-comm
  }

-- Combining them: Cost = ([0, ∞], ≥, 0, +) is a symmetric monoidal preorder
Cost = record
  { preorder = Cost-preorder
  ; structure = Cost-monoidal-structure
  }
```

## Interpretation

The Cost monoidal preorder captures the idea of cost or distance:

**(a) Monotonicity (x₁ ≥ y₁ and x₂ ≥ y₂ implies x₁ + x₂ ≥ y₁ + y₂):** If path 1 costs at most x₁ and path 2 costs at most x₂, then combining them costs at most x₁ + x₂.

**(b) Unit (0 + x = x):** Starting at a location and staying there has zero cost.

**(c) Associativity:** The total cost is independent of how we group the calculation.

**(d) Symmetry:** The order of adding costs doesn't matter.

The use of ≥ for the ordering means that a morphism with cost c exists whenever the actual cost is at most c. This captures the "at most" interpretation mentioned in the textbook.
```
