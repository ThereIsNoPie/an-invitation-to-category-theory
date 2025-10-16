---
layout: agda
title: "Monotone Map"
section: "Definitions"
chapter: 1
number: 54
---

# Monotone Map

**Definition 1.54.** A *monotone map* between preorders (A, ≤_A) and (B, ≤_B) is a function f : A → B such that, for all elements x, y ∈ A, if x ≤_A y then f(x) ≤_B f(y).

```agda
module definitions.MonotoneMap where

open import definitions.Preorder using (Preorder)
open import Data.Product using (Σ; Σ-syntax)

-- A monotone map between preorders (A, ≤_A) and (B, ≤_B) is a function
-- f : A → B such that for all x, y ∈ A, if x ≤_A y then f(x) ≤_B f(y)

-- Monotonic functions (order-preserving)
Monotonic : {A B : Set} → (_≤₁_ : A → A → Set) → (_≤₂_ : B → B → Set) → (A → B) → Set
Monotonic _≤₁_ _≤₂_ f = ∀ {x y} → x ≤₁ y → f x ≤₂ f y

-- Monotonic function between preorders
_⇒_ : Preorder → Preorder → Set
P ⇒ Q = let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
            open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
        in Σ[ f ∈ (A → B) ] (Monotonic _≤₁_ _≤₂_ f)

MonotoneMap : Preorder → Preorder → Set
MonotoneMap P Q = P ⇒ Q
```
