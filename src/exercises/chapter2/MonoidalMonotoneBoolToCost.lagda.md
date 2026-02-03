---
layout: agda
title: "Monoidal Monotone from Bool to Cost"
section: "Exercises"
chapter: 2
number: 27
---

# Exercise 2.27: Monoidal Monotone from Bool to Cost

## Textbook Exercise

**Exercise 2.27.** Recall Bool = (B, ≤, true, ∧) from Example 2.12 and Cost = ([0, ∞], ≥, 0, +) from Example 2.21. There is a monoidal monotone g : Bool → Cost, given by g(false) := ∞ and g(true) := 0.

1. Check that the map g : (B, ≤, true, ∧) → ([0, ∞], ≥, 0, +) presented above indeed
   - is monotonic,
   - satisfies condition (a) of Definition 2.25,
   - satisfies condition (b) of Definition 2.25.
2. Is g strict?

## Agda Setup

```agda
module exercises.chapter2.MonoidalMonotoneBoolToCost where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter1.MonotoneMap using (Monotonic)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import definitions.chapter2.MonoidalMonotone
  using (IsMonoidalMonotone; IsStrictMonoidalMonotone)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤; ≤-trans; ≤-refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
```

## Problem

Define the Bool monoidal preorder and a concrete Cost-like monoidal preorder using extended natural numbers, then verify the map g is a monoidal monotone and determine if it is strict.

```agda
-- Define the ordering on Bool: false ≤ true
data _≤Bool_ : Bool → Bool → Set where
  false≤false : false ≤Bool false
  false≤true  : false ≤Bool true
  true≤true   : true ≤Bool true

-- Extended naturals: ℕ ∪ {∞}
data ℕ∞ : Set where
  fin : ℕ → ℕ∞
  ∞   : ℕ∞

-- Reverse ordering on ℕ∞ (greater-than-or-equal, matching Cost from the textbook)
data _≥∞_ : ℕ∞ → ℕ∞ → Set where
  ∞≥∞   : ∞ ≥∞ ∞
  ∞≥fin : ∀ {n} → ∞ ≥∞ fin n
  fin≥fin : ∀ {m n} → m ≤ n → fin n ≥∞ fin m

-- Addition on ℕ∞
_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
fin m +∞ fin n = fin (m + n)
∞ +∞ _ = ∞
_ +∞ ∞ = ∞
```

## Solution

**Strategy:** We define the Bool monoidal preorder with false ≤ true, unit = true, and product = ∧. For Cost, we use ℕ∞ with ≥∞ ordering, unit = 0, and product = +∞. Then we define g(false) = ∞ and g(true) = fin 0, and verify each condition.

```agda
-- Bool with ≤Bool is a preorder
≤Bool-refl : ∀ {x : Bool} → x ≤Bool x
≤Bool-refl {false} = false≤false
≤Bool-refl {true} = true≤true

≤Bool-trans : ∀ {x y z : Bool} → x ≤Bool y → y ≤Bool z → x ≤Bool z
≤Bool-trans false≤false false≤false = false≤false
≤Bool-trans false≤false false≤true = false≤true
≤Bool-trans false≤true true≤true = false≤true
≤Bool-trans true≤true true≤true = true≤true

Bool-preorder : Preorder
Bool-preorder = record
  { Carrier = Bool
  ; _≤_ = _≤Bool_
  ; isPreorder = record
      { reflexive = ≤Bool-refl
      ; transitive = ≤Bool-trans
      }
  }

-- ∧ is monotonic with respect to ≤Bool
∧-monotonic : ∀ {x₁ x₂ y₁ y₂ : Bool} → x₁ ≤Bool y₁ → x₂ ≤Bool y₂ → (x₁ ∧ x₂) ≤Bool (y₁ ∧ y₂)
∧-monotonic false≤false false≤false = false≤false
∧-monotonic false≤false false≤true = false≤false
∧-monotonic false≤false true≤true = false≤false
∧-monotonic false≤true false≤false = false≤false
∧-monotonic false≤true false≤true = false≤true
∧-monotonic false≤true true≤true = false≤true
∧-monotonic true≤true false≤false = false≤false
∧-monotonic true≤true false≤true = false≤true
∧-monotonic true≤true true≤true = true≤true

-- true is the left identity for ∧
∧-identityˡ : ∀ {x : Bool} → true ∧ x ≡ x
∧-identityˡ {false} = refl
∧-identityˡ {true} = refl

-- true is the right identity for ∧
∧-identityʳ : ∀ {x : Bool} → x ∧ true ≡ x
∧-identityʳ {false} = refl
∧-identityʳ {true} = refl

-- ∧ is associative
∧-assoc : ∀ (x y z : Bool) → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
∧-assoc false y z = refl
∧-assoc true y z = refl

-- ∧ is commutative
∧-comm : ∀ (x y : Bool) → x ∧ y ≡ y ∧ x
∧-comm false false = refl
∧-comm false true = refl
∧-comm true false = refl
∧-comm true true = refl

-- The monoidal structure on Bool: (true, ∧)
Bool-monoidal-structure : SymmetricMonoidalStructure Bool-preorder
Bool-monoidal-structure = record
  { I = true
  ; _⊗_ = _∧_
  ; monotonicity = ∧-monotonic
  ; left-unit = ∧-identityˡ
  ; right-unit = ∧-identityʳ
  ; associativity = λ {x} {y} {z} → ∧-assoc x y z
  ; symmetry = λ {x} {y} → ∧-comm x y
  }

-- Bool = (Bool, ≤Bool, true, ∧) is a symmetric monoidal preorder
Bool-monoidal : SymmetricMonoidalPreorder
Bool-monoidal = record
  { preorder = Bool-preorder
  ; structure = Bool-monoidal-structure
  }

-- ℕ∞ with ≥∞ is a preorder
≥∞-refl : ∀ {x : ℕ∞} → x ≥∞ x
≥∞-refl {fin n} = fin≥fin ≤-refl
≥∞-refl {∞} = ∞≥∞

≥∞-trans : ∀ {x y z : ℕ∞} → x ≥∞ y → y ≥∞ z → x ≥∞ z
≥∞-trans ∞≥∞ ∞≥∞ = ∞≥∞
≥∞-trans ∞≥∞ ∞≥fin = ∞≥fin
≥∞-trans ∞≥fin (fin≥fin _) = ∞≥fin
≥∞-trans (fin≥fin m≤n) (fin≥fin n≤p) = fin≥fin (≤-trans n≤p m≤n)

Cost-preorder : Preorder
Cost-preorder = record
  { Carrier = ℕ∞
  ; _≤_ = _≥∞_
  ; isPreorder = record
      { reflexive = ≥∞-refl
      ; transitive = ≥∞-trans
      }
  }

-- +∞ is monotonic with respect to ≥∞
+∞-mono : ∀ {x₁ x₂ y₁ y₂ : ℕ∞} → x₁ ≥∞ y₁ → x₂ ≥∞ y₂ → (x₁ +∞ x₂) ≥∞ (y₁ +∞ y₂)
+∞-mono {∞} {∞} {∞} {∞} ∞≥∞ ∞≥∞ = ∞≥∞
+∞-mono {∞} {∞} {∞} {fin l} ∞≥∞ ∞≥fin = ∞≥∞
+∞-mono {∞} {∞} {fin n} {∞} ∞≥fin ∞≥∞ = ∞≥∞
+∞-mono {∞} {∞} {fin n} {fin l} ∞≥fin ∞≥fin = ∞≥fin
+∞-mono {∞} {fin m} {∞} {fin l} ∞≥∞ (fin≥fin _) = ∞≥∞
+∞-mono {∞} {fin m} {fin n} {fin l} ∞≥fin (fin≥fin _) = ∞≥fin
+∞-mono {fin i} {∞} {fin k} {∞} (fin≥fin _) ∞≥∞ = ∞≥∞
+∞-mono {fin i} {∞} {fin k} {fin l} (fin≥fin _) ∞≥fin = ∞≥fin
+∞-mono {fin i} {fin j} {fin k} {fin l} (fin≥fin m≤n) (fin≥fin p≤q) = fin≥fin (+-mono-≤ m≤n p≤q)

-- fin 0 is the left identity for +∞
+∞-identityˡ : ∀ {x : ℕ∞} → fin 0 +∞ x ≡ x
+∞-identityˡ {fin n} = refl
+∞-identityˡ {∞} = refl

-- fin 0 is the right identity for +∞
+∞-identityʳ : ∀ {x : ℕ∞} → x +∞ fin 0 ≡ x
+∞-identityʳ {fin n} rewrite +-identityʳ n = refl
+∞-identityʳ {∞} = refl

-- +∞ is associative
+∞-assoc : ∀ {x y z : ℕ∞} → (x +∞ y) +∞ z ≡ x +∞ (y +∞ z)
+∞-assoc {fin m} {fin n} {fin p} = cong fin (+-assoc m n p)
+∞-assoc {fin m} {fin n} {∞} = refl
+∞-assoc {fin m} {∞} {z} = refl
+∞-assoc {∞} {y} {z} = refl

-- +∞ is commutative
+∞-comm : ∀ {x y : ℕ∞} → x +∞ y ≡ y +∞ x
+∞-comm {fin m} {fin n} = cong fin (+-comm m n)
+∞-comm {fin m} {∞} = refl
+∞-comm {∞} {fin n} = refl
+∞-comm {∞} {∞} = refl

-- The monoidal structure on ℕ∞: (fin 0, +∞)
Cost-monoidal-structure : SymmetricMonoidalStructure Cost-preorder
Cost-monoidal-structure = record
  { I = fin 0
  ; _⊗_ = _+∞_
  ; monotonicity = +∞-mono
  ; left-unit = +∞-identityˡ
  ; right-unit = +∞-identityʳ
  ; associativity = +∞-assoc
  ; symmetry = +∞-comm
  }

-- Cost = (ℕ∞, ≥∞, fin 0, +∞) is a symmetric monoidal preorder
Cost : SymmetricMonoidalPreorder
Cost = record
  { preorder = Cost-preorder
  ; structure = Cost-monoidal-structure
  }

-- The map g : Bool → ℕ∞
g : Bool → ℕ∞
g false = ∞
g true = fin 0

-- Part 1: Verify g is a monoidal monotone

-- g is monotonic: if x ≤Bool y then g(x) ≥∞ g(y)
g-monotonic : Monotonic _≤Bool_ _≥∞_ g
g-monotonic false≤false = ∞≥∞
g-monotonic false≤true = ∞≥fin
g-monotonic true≤true = fin≥fin z≤n

-- Condition (a): I_Cost ≤_Cost g(I_Bool)
-- i.e., fin 0 ≥∞ g(true) = fin 0
g-preserves-unit : fin 0 ≥∞ g true
g-preserves-unit = fin≥fin z≤n

-- Condition (b): g(x) ⊗_Cost g(y) ≤_Cost g(x ⊗_Bool y)
-- i.e., g(x) +∞ g(y) ≥∞ g(x ∧ y)
g-preserves-mult : ∀ {x y : Bool} → (g x +∞ g y) ≥∞ g (x ∧ y)
g-preserves-mult {false} {false} = ∞≥∞
g-preserves-mult {false} {true} = ∞≥∞
g-preserves-mult {true} {false} = ∞≥∞
g-preserves-mult {true} {true} = fin≥fin z≤n

g-is-monoidal-monotone : IsMonoidalMonotone Bool-monoidal Cost g
g-is-monoidal-monotone = record
  { monotone = g-monotonic
  ; preserves-unit = g-preserves-unit
  ; preserves-mult = g-preserves-mult
  }

-- Part 2: Check if g is strict

-- g(x) +∞ g(y) = g(x ∧ y) for all x, y : Bool
g-preserves-mult-≡ : ∀ {x y : Bool} → (g x +∞ g y) ≡ g (x ∧ y)
g-preserves-mult-≡ {false} {false} = refl
g-preserves-mult-≡ {false} {true} = refl
g-preserves-mult-≡ {true} {false} = refl
g-preserves-mult-≡ {true} {true} = refl

g-is-strict : IsStrictMonoidalMonotone Bool-monoidal Cost g
g-is-strict = record
  { monotone = g-monotonic
  ; preserves-unit-≡ = refl  -- fin 0 = g(true)
  ; preserves-mult-≡ = g-preserves-mult-≡
  }
```

## Answer

**Yes, g is strict.** The map g : Bool → Cost satisfies the strict monoidal monotone conditions with equality (not just inequality). This is because:

1. The unit condition is exact: fin 0 = g(true)
2. The multiplication preservation is exact: g(x) + g(y) = g(x ∧ y) for all x, y ∈ Bool

The key insight is that g maps the boolean "success/failure" structure (where true represents success and false represents failure) to costs in a canonical way: success costs nothing (fin 0) and failure costs infinitely (∞).
```
