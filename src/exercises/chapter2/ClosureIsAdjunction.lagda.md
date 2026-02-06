---
layout: agda
title: "Closure Is Adjunction"
section: "Exercises"
chapter: 2
number: 59
---

# Closure Is Adjunction

## Textbook

**Exercise 2.59.** Condition (2.23) says precisely that there is a Galois connection in the sense of Definition 1.90. Let's prove this fact. In particular, we'll prove that a monoidal preorder is monoidal closed iff, given any $v \in V$, the map $(-\otimes v) : V \to V$ given by multiplying with $v$ has a right adjoint. We write this right adjoint $(v \multimap -) : V \to V$.

1. Using Definition 2.1, show that $(-\otimes v)$ is monotone.
2. Supposing that $\mathcal{V}$ is closed, show that for all $v, w \in V$ we have $(v \multimap w) \otimes v \leq w$.
3. Using part 2, show that $(v \multimap -)$ is monotone.
4. Conclude that a symmetric monoidal preorder is closed if and only if the monotone map $(-\otimes v)$ has a right adjoint.

## Problem

The key insight: the closure condition $(a \otimes v) \leq w \iff a \leq (v \multimap w)$ is *exactly* the definition of a Galois connection between $(-\otimes v)$ and $(v \multimap -)$.

```agda
module exercises.chapter2.ClosureIsAdjunction where

open import definitions.chapter2.MonoidalClosed
  using (MonoidalClosedPreorder; IsMonoidalClosed)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import definitions.chapter1.MonotoneMap using (Monotonic)
open import definitions.chapter1.GaloisConnection using (GaloisConnection)
open import definitions.chapter1.Preorder using (Preorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

module ClosureAdjunction (MCP : MonoidalClosedPreorder) where
  open MonoidalClosedPreorder MCP

  -- Part 1: (-⊗v) is monotone
  ⊗v-monotone : ∀ {v} → Monotonic _≤_ _≤_ (_⊗ v)

  -- Part 2: Evaluation — (v ⊸ w) ⊗ v ≤ w
  eval : ∀ {v w} → ((v ⊸ w) ⊗ v) ≤ w

  -- Part 3: (v ⊸ -) is monotone
  ⊸-monotone : ∀ {v} → Monotonic _≤_ _≤_ (v ⊸_)

  -- Part 4: The closure condition is a Galois connection
  --   (-⊗v) is left adjoint to (v⊸-)
  closure-is-galois : ∀ {v} → GaloisConnection preorder preorder
```

## Solution

```agda
  -- Part 1: monotonicity of (-⊗v) follows directly from the monoidal structure
  ⊗v-monotone a≤b = monotonicity a≤b reflexive

  -- Part 2: uncurry reflexivity of (v ⊸ w) ≤ (v ⊸ w)
  eval = uncurry reflexive

  -- Part 3: if w ≤ w', then (v ⊸ w) ≤ (v ⊸ w')
  -- Proof: eval gives (v ⊸ w) ⊗ v ≤ w ≤ w', then curry.
  ⊸-monotone w≤w' = curry (transitive eval w≤w')

  -- Part 4: package everything into a GaloisConnection record
  closure-is-galois {v} = record
    { f   = _⊗ v
    ; g   = v ⊸_
    ; f-g = curry
    ; g-f = uncurry
    }
```
