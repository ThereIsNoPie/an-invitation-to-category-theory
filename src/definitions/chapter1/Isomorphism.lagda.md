---
layout: agda
title: "Isomorphism"
section: "Definitions"
chapter: 1
number: 70
---

# Isomorphism

**Definition 1.70.** Let (P, ≤_P) and (Q, ≤_Q) be preorders. A monotone function f : P → Q is called an *isomorphism* if there exists a monotone function g : Q → P such that f ; g = id_P and g ; f = id_Q. This means that, for any p ∈ P and q ∈ Q, we have

p = g(f(p)) and q = f(g(q)).

We refer to g as the *inverse* of f, and vice versa: f is the inverse of g.

If there is an isomorphism P → Q, we say that P and Q are *isomorphic*.

```agda
module definitions.chapter1.Isomorphism where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.MonotoneMap using (_⇒_)
open import definitions.chapter1.Composition using (_⨾_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Isomorphism between preorders
record _≅_ (P Q : Preorder) : Set where
  open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)

  field
    -- Forward monotone function f : P → Q
    to : P ⇒ Q

    -- Inverse monotone function g : Q → P
    from : Q ⇒ P

    -- f ; g = id_P: for any p ∈ P, we have p = g(f(p))
    left-inverse : ∀ (p : A) → proj₁ from (proj₁ to p) ≡ p

    -- g ; f = id_Q: for any q ∈ Q, we have q = f(g(q))
    right-inverse : ∀ (q : B) → proj₁ to (proj₁ from q) ≡ q

-- P and Q are isomorphic if there exists an isomorphism P → Q
Isomorphic : Preorder → Preorder → Set
Isomorphic P Q = P ≅ Q
```
