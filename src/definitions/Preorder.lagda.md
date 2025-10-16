---
layout: agda
title: "Preorder"
section: "Definitions"
chapter: 1
number: 25
---

# Preorder

**Definition 1.25.** A *preorder relation* on a set X is a binary relation on X, here denoted with infix notation ≤, such that

(a) x ≤ x; and

(b) if x ≤ y and y ≤ z, then x ≤ z.

The first condition is called *reflexivity* and the second is called *transitivity*. If x ≤ y and y ≤ x, we write x ≅ y and say x and y are *equivalent*. We call a pair (X, ≤) consisting of a set equipped with a preorder relation a *preorder*.

```agda
module definitions.Preorder where

open import Data.Product using (_×_)

-- A preorder relation on a set X is a binary relation satisfying
-- reflexivity and transitivity
record IsPreorder {A : Set} (_≤_ : A → A → Set) : Set where
  field
    -- (a) Reflexivity: x ≤ x
    reflexive  : ∀ {x} → x ≤ x

    -- (b) Transitivity: if x ≤ y and y ≤ z, then x ≤ z
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

  -- If x ≤ y and y ≤ x, we write x ≅ y and say x and y are equivalent
  _≅_ : A → A → Set
  x ≅ y = (x ≤ y) × (y ≤ x)

-- A preorder is a pair (X, ≤) consisting of a set equipped with
-- a preorder relation
record Preorder : Set₁ where
  field
    Carrier    : Set
    _≤_        : Carrier → Carrier → Set
    isPreorder : IsPreorder _≤_

  open IsPreorder isPreorder public

  -- Equational reasoning for preorders
  module ≤-Reasoning where
    infix  3 _∎
    infixr 2 _≤⟨_⟩_
    infix  1 begin_

    begin_ : ∀ {x y} → x ≤ y → x ≤ y
    begin p = p

    _≤⟨_⟩_ : ∀ x {y z} → x ≤ y → y ≤ z → x ≤ z
    x ≤⟨ p ⟩ q = transitive p q

    _∎ : ∀ x → x ≤ x
    x ∎ = reflexive
```
