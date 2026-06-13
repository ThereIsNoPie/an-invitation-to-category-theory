---
layout: agda
title: "Booleans with OR"
section: "Exercises"
chapter: 2
number: 12
---

# Booleans with OR

## Textbook Exercise

**Exercise 2.12.** Let $(\mathbb{B}, \leq)$ be as above, but now consider the monoidal product to be $\vee$ (OR).

$$
\begin{array}{c|cc}
\vee & \mathsf{false} & \mathsf{true} \\\hline
\mathsf{false} & \mathsf{false} & \mathsf{true} \\
\mathsf{true} & \mathsf{true} & \mathsf{true}
\end{array}
$$

What must the monoidal unit be in order to satisfy the conditions of Definition 2.1? Does it satisfy the rest of the conditions?

## Agda Setup

```agda
module exercises.chapter2.BoolOr where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder; SymmetricMonoidalStructure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; _∨_)
```

## The Boolean Preorder

We reuse the same ordering: false ≤ true.

```agda
data _≤𝔹_ : Bool → Bool → Set where
  ≤-refl : ∀ {x} → x ≤𝔹 x
  f≤t : false ≤𝔹 true

≤𝔹-trans : ∀ {x y z} → x ≤𝔹 y → y ≤𝔹 z → x ≤𝔹 z
≤𝔹-trans ≤-refl q = q
≤𝔹-trans f≤t ≤-refl = f≤t

𝔹-preorder : Preorder
𝔹-preorder = record
  { Carrier = Bool
  ; _≤_ = _≤𝔹_
  ; isPreorder = record { reflexive = ≤-refl ; transitive = ≤𝔹-trans }
  }
```

## Problem

Which choice of monoidal unit $I$ makes $(\mathbb{B}, \leq, I, \vee)$ a
symmetric monoidal preorder — and do all the conditions of Definition 2.1 hold?

```agda
𝔹∨-structure : SymmetricMonoidalStructure 𝔹-preorder

Bool∨-SMP : SymmetricMonoidalPreorder
```

## Solution

**Answer:** The monoidal unit must be $\mathsf{false}$.

For unitality we need: $I \vee x = x$ and $x \vee I = x$ for all $x$.
- If $I = \mathsf{true}$: $\mathsf{true} \vee x = \mathsf{true} \neq x$ when $x = \mathsf{false}$. ✗
- If $I = \mathsf{false}$: $\mathsf{false} \vee x = x$ ✓ and $x \vee \mathsf{false} = x$ ✓

The remaining conditions are finite case checks:

```agda
-- Monotonicity: x₁ ≤ y₁ and x₂ ≤ y₂ implies (x₁ ∨ x₂) ≤ (y₁ ∨ y₂)
∨-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤𝔹 y₁ → x₂ ≤𝔹 y₂ → (x₁ ∨ x₂) ≤𝔹 (y₁ ∨ y₂)
∨-mono ≤-refl ≤-refl = ≤-refl
∨-mono ≤-refl f≤t = ∨-mono-right _ where
  ∨-mono-right : ∀ b → (b ∨ false) ≤𝔹 (b ∨ true)
  ∨-mono-right false = f≤t
  ∨-mono-right true = ≤-refl
∨-mono f≤t ≤-refl = ∨-mono-left _ where
  ∨-mono-left : ∀ b → (false ∨ b) ≤𝔹 (true ∨ b)
  ∨-mono-left false = f≤t
  ∨-mono-left true = ≤-refl
∨-mono f≤t f≤t = f≤t  -- false ∨ false = false ≤ true = true ∨ true

-- Symmetry: x ∨ y = y ∨ x
∨-comm : ∀ {x y} → x ∨ y ≡ y ∨ x
∨-comm {false} {false} = refl
∨-comm {false} {true} = refl
∨-comm {true} {false} = refl
∨-comm {true} {true} = refl

-- Associativity: (x ∨ y) ∨ z = x ∨ (y ∨ z)
∨-assoc : ∀ {x y z} → (x ∨ y) ∨ z ≡ x ∨ (y ∨ z)
∨-assoc {false} = refl
∨-assoc {true} = refl

-- Left unit: false ∨ x = x
∨-identityˡ : ∀ {x} → false ∨ x ≡ x
∨-identityˡ = refl

-- Right unit: x ∨ false = x
∨-identityʳ : ∀ {x} → x ∨ false ≡ x
∨-identityʳ {false} = refl
∨-identityʳ {true} = refl

𝔹∨-structure = record
  { I = false
  ; _⊗_ = _∨_
  ; monotonicity = ∨-mono
  ; left-unit = ∨-identityˡ
  ; right-unit = ∨-identityʳ
  ; associativity = λ {x} {y} {z} → ∨-assoc {x} {y} {z}
  ; symmetry = λ {x} {y} → ∨-comm {x} {y}
  }
```

```agda
Bool∨-SMP = record
  { preorder = 𝔹-preorder
  ; structure = 𝔹∨-structure
  }
```

## Interpretation

Yes, all conditions are satisfied with $I = \mathsf{false}$:
- **Monotonicity**: If $x_1 \leq y_1$ and $x_2 \leq y_2$, then $x_1 \vee x_2 \leq y_1 \vee y_2$ ✓
- **Unitality**: $\mathsf{false} \vee x = x$ and $x \vee \mathsf{false} = x$ ✓
- **Associativity**: $(x \vee y) \vee z = x \vee (y \vee z)$ ✓
- **Symmetry**: $x \vee y = y \vee x$ ✓
