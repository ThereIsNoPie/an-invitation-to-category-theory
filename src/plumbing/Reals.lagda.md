---
layout: agda
title: "Real Numbers"
section: "Plumbing"
---

# Real Numbers

General postulates for real numbers. These define the reals as a mathematical structure, independent of any specific application.

```agda
module plumbing.Reals where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
```

## The Real Numbers ℝ

```agda
postulate
  ℝ : Set
```

## Ordering

```agda
postulate
  _≤ℝ_ : ℝ → ℝ → Set
  _<ℝ_ : ℝ → ℝ → Set
  _≥ℝ_ : ℝ → ℝ → Set

  ≤ℝ-refl : ∀ {x : ℝ} → x ≤ℝ x
  ≤ℝ-trans : ∀ {x y z : ℝ} → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
  ≤ℝ-antisym : ∀ {x y : ℝ} → x ≤ℝ y → y ≤ℝ x → x ≡ y

infix 4 _≤ℝ_ _<ℝ_ _≥ℝ_
```

## Arithmetic

```agda
postulate
  0ℝ : ℝ
  1ℝ : ℝ
  _+_ : ℝ → ℝ → ℝ
  _-_ : ℝ → ℝ → ℝ
  _*_ : ℝ → ℝ → ℝ
  -_ : ℝ → ℝ  -- negation

infixl 6 _+_ _-_
infixl 7 _*_
infix 8 -_
```

## Field Properties

We postulate the minimal set and derive the rest.

```agda
postulate
  -- Addition (core)
  +-identityˡ : ∀ {x : ℝ} → 0ℝ + x ≡ x
  +-assoc : ∀ {x y z : ℝ} → (x + y) + z ≡ x + (y + z)
  +-comm : ∀ {x y : ℝ} → x + y ≡ y + x
  +-inverseˡ : ∀ {x : ℝ} → (- x) + x ≡ 0ℝ

  -- Multiplication (core)
  *-identityˡ : ∀ {x : ℝ} → 1ℝ * x ≡ x
  *-assoc : ∀ {x y z : ℝ} → (x * y) * z ≡ x * (y * z)
  *-comm : ∀ {x y : ℝ} → x * y ≡ y * x

  -- Distributivity
  *-distribˡ : ∀ {x y z : ℝ} → x * (y + z) ≡ (x * y) + (x * z)

  -- Subtraction definition
  x-y≡x+-y : ∀ {x y : ℝ} → x - y ≡ x + (- y)

-- Derived from commutativity
+-identityʳ : ∀ {x : ℝ} → x + 0ℝ ≡ x
+-identityʳ = trans +-comm +-identityˡ

+-inverseʳ : ∀ {x : ℝ} → x + (- x) ≡ 0ℝ
+-inverseʳ = trans +-comm +-inverseˡ

*-identityʳ : ∀ {x : ℝ} → x * 1ℝ ≡ x
*-identityʳ = trans *-comm *-identityˡ

*-distribʳ : ∀ {x y z : ℝ} → (x + y) * z ≡ (x * z) + (y * z)
*-distribʳ {x} {y} {z} = trans *-comm (trans *-distribˡ (trans (cong₂ _+_ *-comm *-comm) refl))
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B}
          → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
    cong₂ f refl refl = refl
```

## Ordered Field Properties

```agda
postulate
  +-mono : ∀ {x₁ x₂ y₁ y₂ : ℝ} → x₁ ≤ℝ y₁ → x₂ ≤ℝ y₂ → (x₁ + x₂) ≤ℝ (y₁ + y₂)
  *-mono-pos : ∀ {x y z : ℝ} → 0ℝ ≤ℝ z → x ≤ℝ y → (x * z) ≤ℝ (y * z)
```

## Absolute Value

```agda
postulate
  ∣_∣ : ℝ → ℝ

  ∣x∣≥0 : ∀ {x : ℝ} → 0ℝ ≤ℝ ∣ x ∣
  ∣0∣≡0 : ∣ 0ℝ ∣ ≡ 0ℝ
  ∣-x∣≡∣x∣ : ∀ {x : ℝ} → ∣ - x ∣ ≡ ∣ x ∣
  ∣x*y∣≡∣x∣*∣y∣ : ∀ {x y : ℝ} → ∣ x * y ∣ ≡ ∣ x ∣ * ∣ y ∣
  ∣x+y∣≤∣x∣+∣y∣ : ∀ {x y : ℝ} → ∣ x + y ∣ ≤ℝ (∣ x ∣ + ∣ y ∣)  -- triangle inequality
  ∣x∣≡0→x≡0 : ∀ {x : ℝ} → ∣ x ∣ ≡ 0ℝ → x ≡ 0ℝ
```

---

# Extended Nonnegative Reals [0, ∞]

For metric spaces and Cost, we need [0, ∞] = ℝ≥0 ∪ {∞}.

```agda
postulate
  [0,∞] : Set

  -- Embedding from ℝ (partial - only for nonnegative)
  ιℝ : ℝ → [0,∞]

  -- Distinguished elements
  0∞ : [0,∞]
  ∞ : [0,∞]

  -- Ordering (reversed: ≥ for Cost)
  _≥_ : [0,∞] → [0,∞] → Set

  -- Addition
  _+ℝ_ : [0,∞] → [0,∞] → [0,∞]

infixl 6 _+ℝ_
infix 4 _≥_
```

## [0, ∞] Properties

```agda
postulate
  -- Ordering
  ≥-refl : ∀ {x : [0,∞]} → x ≥ x
  ≥-trans : ∀ {x y z : [0,∞]} → x ≥ y → y ≥ z → x ≥ z
  ≥-antisym : ∀ {x y : [0,∞]} → x ≥ y → y ≥ x → x ≡ y
  ∞-greatest : ∀ {x : [0,∞]} → ∞ ≥ x
  0-least : ∀ {x : [0,∞]} → x ≥ 0∞

  -- Addition (core)
  +ℝ-identityˡ : ∀ {x : [0,∞]} → 0∞ +ℝ x ≡ x
  +ℝ-assoc : ∀ {x y z : [0,∞]} → (x +ℝ y) +ℝ z ≡ x +ℝ (y +ℝ z)
  +ℝ-comm : ∀ {x y : [0,∞]} → x +ℝ y ≡ y +ℝ x
  +ℝ-mono : ∀ {x₁ x₂ y₁ y₂ : [0,∞]} → x₁ ≥ y₁ → x₂ ≥ y₂ → (x₁ +ℝ x₂) ≥ (y₁ +ℝ y₂)
  +ℝ-∞ˡ : ∀ {x : [0,∞]} → ∞ +ℝ x ≡ ∞

-- Derived from commutativity
+ℝ-identityʳ : ∀ {x : [0,∞]} → x +ℝ 0∞ ≡ x
+ℝ-identityʳ = trans +ℝ-comm +ℝ-identityˡ

+ℝ-∞ʳ : ∀ {x : [0,∞]} → x +ℝ ∞ ≡ ∞
+ℝ-∞ʳ = trans +ℝ-comm +ℝ-∞ˡ
```

---

# Metric Space Adaptations

Properties connecting ℝ to metric space concepts via distance.

```agda
postulate
  -- Distance function (|x - y| lifted to [0,∞])
  dist : ℝ → ℝ → [0,∞]

  -- Self-distance is zero
  dist-refl : ∀ {x : ℝ} → dist x x ≡ 0∞

  -- Symmetry
  dist-sym : ∀ {x y : ℝ} → dist x y ≡ dist y x

  -- Triangle inequality for distances
  dist-triangle : ∀ {x y z : ℝ} → (dist x y +ℝ dist y z) ≥ dist x z

  -- Separation
  dist-zero→eq : ∀ {x y : ℝ} → dist x y ≡ 0∞ → x ≡ y
```
