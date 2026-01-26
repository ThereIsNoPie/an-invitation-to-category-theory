---
layout: agda
title: "Booleans with AND"
section: "Examples"
chapter: 2
number: 11
---

# Booleans with AND

## Textbook Description

**Example 2.11.** We can define a monoidal structure on $\mathbb{B} = \{\mathsf{true}, \mathsf{false}\}$ with $\mathsf{false} \leq \mathsf{true}$ by letting the monoidal unit be $\mathsf{true}$ and the monoidal product be $\wedge$ (AND).

$$
\begin{array}{c|cc}
\wedge & \mathsf{false} & \mathsf{true} \\\hline
\mathsf{false} & \mathsf{false} & \mathsf{false} \\
\mathsf{true} & \mathsf{false} & \mathsf{true}
\end{array}
$$

One can check that all the properties in Definition 2.1 hold, so we have a monoidal preorder $\mathbf{Bool} := (\mathbb{B}, \leq, \mathsf{true}, \wedge)$.

## Agda Setup

```agda
module examples.chapter2.BoolAnd where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder; SymmetricMonoidalStructure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; _∧_)
```

## The Boolean Preorder

The order is: false ≤ true (and reflexively).

```agda
-- The ordering relation: false ≤ true
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

## The Symmetric Monoidal Structure

```agda
-- Monotonicity: x₁ ≤ y₁ and x₂ ≤ y₂ implies (x₁ ∧ x₂) ≤ (y₁ ∧ y₂)
∧-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤𝔹 y₁ → x₂ ≤𝔹 y₂ → (x₁ ∧ x₂) ≤𝔹 (y₁ ∧ y₂)
∧-mono ≤-refl ≤-refl = ≤-refl
∧-mono ≤-refl f≤t = ∧-mono-right _ where
  ∧-mono-right : ∀ b → (b ∧ false) ≤𝔹 (b ∧ true)
  ∧-mono-right false = ≤-refl
  ∧-mono-right true = f≤t
∧-mono f≤t ≤-refl = ∧-mono-left _ where
  ∧-mono-left : ∀ b → (false ∧ b) ≤𝔹 (true ∧ b)
  ∧-mono-left false = ≤-refl
  ∧-mono-left true = f≤t
∧-mono f≤t f≤t = f≤t  -- false ∧ false = false ≤ true = true ∧ true

-- Symmetry: x ∧ y = y ∧ x
∧-comm : ∀ {x y} → x ∧ y ≡ y ∧ x
∧-comm {false} {false} = refl
∧-comm {false} {true} = refl
∧-comm {true} {false} = refl
∧-comm {true} {true} = refl

-- Associativity: (x ∧ y) ∧ z = x ∧ (y ∧ z)
∧-assoc : ∀ {x y z} → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
∧-assoc {false} = refl
∧-assoc {true} = refl

-- Left unit: true ∧ x = x
∧-identityˡ : ∀ {x} → true ∧ x ≡ x
∧-identityˡ = refl

-- Right unit: x ∧ true = x
∧-identityʳ : ∀ {x} → x ∧ true ≡ x
∧-identityʳ {false} = refl
∧-identityʳ {true} = refl

𝔹-structure : SymmetricMonoidalStructure 𝔹-preorder
𝔹-structure = record
  { I = true
  ; _⊗_ = _∧_
  ; monotonicity = ∧-mono
  ; left-unit = ∧-identityˡ
  ; right-unit = ∧-identityʳ
  ; associativity = λ {x} {y} {z} → ∧-assoc {x} {y} {z}
  ; symmetry = λ {x} {y} → ∧-comm {x} {y}
  }
```

## Bool: The Symmetric Monoidal Preorder

```agda
Bool-SMP : SymmetricMonoidalPreorder
Bool-SMP = record
  { preorder = 𝔹-preorder
  ; structure = 𝔹-structure
  }
```

## Interpretation

$\mathbf{Bool}$ will be important for enrichment. Enriching in Bool means "getting from $a$ to $b$ is a true/false question":
- The monoidal unit being $\mathsf{true}$ means "you can always get from $a$ to $a$"
- The monoidal product being $\wedge$ means "if you can get from $a$ to $b$ AND from $b$ to $c$, then you can get from $a$ to $c$"
