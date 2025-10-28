---
layout: agda
title: "Galois Connection"
section: "Definitions"
chapter: 1
number: 90
---

# Galois Connection

**Definition 1.90.** A *Galois connection* between preorders P and Q is a pair of monotone maps f : P → Q and g : Q → P such that

f(p) ≤ q if and only if p ≤ g(q).   (1.6)

We say that f is the *left adjoint* and g is the *right adjoint* of the Galois connection.

```agda
module definitions.chapter1.GaloisConnection where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.MonotoneMap using (Monotonic)

-- Galois connection between preorders
record GaloisConnection (P Q : Preorder) : Set where
  open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)

  field
    f : A → B  -- Lower adjoint (left adjoint)
    g : B → A  -- Upper adjoint (right adjoint)

    -- Adjunction property: f(x) ≤₂ y  ⟺  x ≤₁ g(y)
    f-g : ∀ {x y} → f x ≤₂ y → x ≤₁ g y
    g-f : ∀ {x y} → x ≤₁ g y → f x ≤₂ y

  -- Derived properties
  f-monotonic : Monotonic _≤₁_ _≤₂_ f
  f-monotonic x≤y = g-f (Preorder.transitive P x≤y (f-g (Preorder.reflexive Q)))

  g-monotonic : Monotonic _≤₂_ _≤₁_ g
  g-monotonic y≤z = f-g (Preorder.transitive Q (g-f (Preorder.reflexive P)) y≤z)
```
