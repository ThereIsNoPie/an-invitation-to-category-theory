---
layout: agda
title: "Monoidal Closed Preorder"
section: "Definitions"
chapter: 2
number: 57
---

# Monoidal Closed Preorder

## Textbook Definition

**Definition 2.57.** A symmetric monoidal preorder $\mathcal{V} = (V, \leq, I, \otimes)$ is called *symmetric monoidal closed* (or just *closed*) if, for every two elements $v, w \in V$, there is an element $v \multimap w$ in $\mathcal{V}$, called the *hom-element*, with the property

$$(a \otimes v) \leq w \quad \text{iff} \quad a \leq (v \multimap w)$$

for all $a, v, w \in V$.

## Interpretation

The condition says that $(-\otimes v)$ and $(v \multimap -)$ form a Galois connection. The hom-element $v \multimap w$ can be thought of as a "single-use $v$-to-$w$ converter": having $a$ resources and $v$ resources is enough to get $w$ if and only if $a$ alone is enough to get a $v$-to-$w$ converter.

## Agda Setup

```agda
module definitions.chapter2.MonoidalClosed where

open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import Data.Product using (_×_; _,_)
```

## Agda Formalization

```agda
-- A symmetric monoidal preorder is closed if it has hom-elements
record IsMonoidalClosed (V : SymmetricMonoidalPreorder) : Set where
  open SymmetricMonoidalPreorder V

  field
    -- The hom-element (internal hom)
    _⊸_ : Carrier → Carrier → Carrier

    -- The closure condition: (a ⊗ v) ≤ w iff a ≤ (v ⊸ w)
    -- We express this as two implications
    curry : ∀ {a v w} → (a ⊗ v) ≤ w → a ≤ (v ⊸ w)
    uncurry : ∀ {a v w} → a ≤ (v ⊸ w) → (a ⊗ v) ≤ w

-- A monoidal closed preorder
record MonoidalClosedPreorder : Set₁ where
  field
    base : SymmetricMonoidalPreorder
    closed : IsMonoidalClosed base

  open SymmetricMonoidalPreorder base public
  open IsMonoidalClosed closed public
```

## Derived Properties

From the closure condition, we can derive useful properties.

```agda
module ClosedProperties (MCP : MonoidalClosedPreorder) where
  open MonoidalClosedPreorder MCP

  -- Evaluation: (v ⊸ w) ⊗ v ≤ w
  -- (Using uncurry with a = v ⊸ w and reflexivity)
  eval : ∀ {v w} → ((v ⊸ w) ⊗ v) ≤ w
  eval = uncurry reflexive

  -- The hom functor is monotone in the second argument
  -- If w ≤ w', then (v ⊸ w) ≤ (v ⊸ w')
  ⊸-mono-r : ∀ {v w w'} → w ≤ w' → (v ⊸ w) ≤ (v ⊸ w')
  ⊸-mono-r {v} {w} {w'} w≤w' = curry (transitive eval w≤w')
```
