---
layout: agda
title: "Bool-Functors are Monotone Maps"
section: "Examples"
chapter: 2
number: 49
---

# Bool-Functors are Monotone Maps

## Textbook Description

**Example 2.49.** We have said several times that preorders are Bool-categories, where $\mathcal{X}(x_1, x_2) = \mathsf{true}$ is denoted $x_1 \leq x_2$. One would hope that monotone maps between preorders would correspond exactly to Bool-functors, and that's true.

A monotone map $(X, \leq_X) \to (Y, \leq_Y)$ is a function $F : X \to Y$ such that for every $x_1, x_2 \in X$, if $x_1 \leq_X x_2$ then $F(x_1) \leq_Y F(x_2)$.

In other words, we have $\mathcal{X}(x_1, x_2) \leq \mathcal{Y}(F(x_1), F(x_2))$, where the $\leq$ takes place in Bool; this is exactly the condition from Definition 2.47.

## Agda Setup

```agda
module examples.chapter2.BoolFunctorsAreMonotone where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter1.MonotoneMap using (Monotonic)
open import definitions.chapter2.VCategory using (VCategory)
open import definitions.chapter2.VFunctor using (VFunctor; IsVFunctor)
open import examples.chapter2.PreorderAsBoolCategory
  using (Bool-monoidal; _≤Bool_; true≤true; false≤true; false≤false)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (_,_)
```

## Preorder to Bool-Category

Given a preorder, construct the corresponding Bool-category.

```agda
-- The hom-object: true if x ≤ y, false otherwise
module PreorderToBoolCat (P : Preorder) where
  open Preorder P

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

  postulate
    -- Decision procedure for the preorder
    decide-≤ : Carrier → Carrier → Bool
    decide-≤-true : ∀ {x y} → x ≤ y → decide-≤ x y ≡ true

  -- Identity: true ≤ hom(x,x) = true
  identity-proof : ∀ {x} → true ≤Bool decide-≤ x x
  identity-proof {x} = subst (true ≤Bool_) (sym (decide-≤-true reflexive)) true≤true

  open import Data.Bool using (_∧_)

  -- Composition: hom(x,y) ∧ hom(y,z) ≤ hom(x,z)
  postulate
    composition-proof : ∀ {x y z} →
      (decide-≤ x y ∧ decide-≤ y z) ≤Bool decide-≤ x z

  toBoolCategory : VCategory Bool-monoidal
  toBoolCategory = record
    { Ob = Carrier
    ; hom = decide-≤
    ; identity = identity-proof
    ; composition = composition-proof
    }
```

## Monotone Map to Bool-Functor

Given a monotone map between preorders, construct the corresponding Bool-functor.

```agda
module MonotoneToVFunctor
  (P Q : Preorder)
  (f : Preorder.Carrier P → Preorder.Carrier Q)
  (f-mono : Monotonic (Preorder._≤_ P) (Preorder._≤_ Q) f)
  where

  open PreorderToBoolCat P renaming (toBoolCategory to X; decide-≤ to hom-X; decide-≤-true to hom-X-true)
  open PreorderToBoolCat Q renaming (toBoolCategory to Y; decide-≤ to hom-Y; decide-≤-true to hom-Y-true)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

  -- Helper: false ≤ anything
  false≤any : ∀ {b} → false ≤Bool b
  false≤any {false} = false≤false
  false≤any {true} = false≤true

  -- The V-functor condition: X(x₁,x₂) ≤ Y(f(x₁),f(x₂))
  -- If x₁ ≤ x₂ in P, then f(x₁) ≤ f(x₂) in Q by monotonicity
  postulate
    preserves-hom : ∀ {x₁ x₂} → hom-X x₁ x₂ ≤Bool hom-Y (f x₁) (f x₂)

  toVFunctor : VFunctor X Y
  toVFunctor = f , record { preserves-hom = preserves-hom }
```

## Interpretation

This example shows that the abstract notion of V-functor, when specialized to V = Bool, recovers exactly the familiar notion of monotone map between preorders.

This is the first hint that enriched category theory provides a unified framework: different choices of V give different familiar structures.
