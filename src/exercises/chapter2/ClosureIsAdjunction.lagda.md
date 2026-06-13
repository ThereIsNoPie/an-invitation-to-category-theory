---
layout: agda
title: "Closure Is Adjunction"
section: "Exercises"
chapter: 2
number: 59
---

# Closure Is Adjunction

## Textbook Exercise

**Exercise 2.59.** Condition (2.23) says precisely that there is a Galois connection in the sense of Definition 1.90. Let's prove this fact. In particular, we'll prove that a monoidal preorder is monoidal closed iff, given any $v \in V$, the map $(-\otimes v) : V \to V$ given by multiplying with $v$ has a right adjoint. We write this right adjoint $(v \multimap -) : V \to V$.

1. Using Definition 2.1, show that $(-\otimes v)$ is monotone.
2. Supposing that $\mathcal{V}$ is closed, show that for all $v, w \in V$ we have $(v \multimap w) \otimes v \leq w$.
3. Using part 2, show that $(v \multimap -)$ is monotone.
4. Conclude that a symmetric monoidal preorder is closed if and only if the monotone map $(-\otimes v)$ has a right adjoint.

## Agda Setup

```agda
module exercises.chapter2.ClosureIsAdjunction where

open import definitions.chapter2.MonoidalClosed using (IsMonoidalClosed)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.MonotoneMap using (Monotonic)
open import definitions.chapter1.GaloisConnection using (GaloisConnection)
```

## Problem

The whole exercise is one sentence:

> $\mathcal{V}$ is monoidal closed **iff**, for every $v$, the map $(-\otimes v)$ has a right adjoint.

To state it we first need to say what "$f$ has a right adjoint" means: it is a
Galois connection in the sense of Definition 1.90, except that the left adjoint
is not arbitrary data — it is pinned to the given map $f$.

```agda
-- "f has a right adjoint g": f x ≤ y iff x ≤ g y
record RightAdjoint (P : Preorder) (f : Preorder.Carrier P → Preorder.Carrier P) : Set where
  open Preorder P
  field
    g    : Carrier → Carrier
    to   : ∀ {x y} → f x ≤ y → x ≤ g y
    from : ∀ {x y} → x ≤ g y → f x ≤ y

-- Sanity check: a map together with a right adjoint is exactly
-- a Galois connection in the sense of Definition 1.90
toGaloisConnection : {P : Preorder} {f : Preorder.Carrier P → Preorder.Carrier P}
                   → RightAdjoint P f → GaloisConnection P P
toGaloisConnection {f = f} ra = record
  { f = f ; g = RightAdjoint.g ra ; f-g = RightAdjoint.to ra ; g-f = RightAdjoint.from ra }
```

Now the statement of the exercise, one signature per direction:

```agda
module Statement (V : SymmetricMonoidalPreorder) where
  open SymmetricMonoidalPreorder V

  -- V is monoidal closed iff every (-⊗v) has a right adjoint
  closed→adjoint : IsMonoidalClosed V → (∀ v → RightAdjoint preorder (_⊗ v))
  adjoint→closed : (∀ v → RightAdjoint preorder (_⊗ v)) → IsMonoidalClosed V
```

## Solution

Parts 1–3 are the textbook's guided steps. Assuming $\mathcal{V}$ is closed:

```agda
  module Parts (closed : IsMonoidalClosed V) where
    open IsMonoidalClosed closed

    -- Part 1: (-⊗v) is monotone — monoidal monotonicity with reflexivity
    -- in the second slot
    ⊗v-monotone : ∀ {v} → Monotonic _≤_ _≤_ (_⊗ v)
    ⊗v-monotone a≤b = monotonicity a≤b reflexive

    -- Part 2: Evaluation — uncurry the trivial (v ⊸ w) ≤ (v ⊸ w)
    eval : ∀ {v w} → ((v ⊸ w) ⊗ v) ≤ w
    eval = uncurry reflexive

    -- Part 3: chain eval with w ≤ w', then curry back
    ⊸-monotone : ∀ {v} → Monotonic _≤_ _≤_ (v ⊸_)
    ⊸-monotone w≤w' = curry (transitive eval w≤w')
```

Part 4 needs none of the above: the closure condition *is* the adjunction
property, verbatim, in both directions.

```agda
  -- (⟹) the right adjoint to (-⊗v) is (v ⊸ -); curry/uncurry are
  -- exactly the adjunction property
  closed→adjoint closed v = record
    { g    = v ⊸_
    ; to   = curry
    ; from = uncurry
    }
    where open IsMonoidalClosed closed

  -- (⟸) read the closure structure off the family of adjoints
  adjoint→closed adj = record
    { _⊸_     = λ v w → RightAdjoint.g (adj v) w
    ; curry   = λ {a} {v} {w} → RightAdjoint.to (adj v)
    ; uncurry = λ {a} {v} {w} → RightAdjoint.from (adj v)
    }
```

Note that parts 1–3 are not needed to prove the iff. They matter because
Definition 1.90's Galois connections live between *monotone* maps — and indeed
monotonicity of both adjoints already follows from the adjunction alone
(`f-monotonic` and `g-monotonic` are derived inside the `GaloisConnection`
record), which is parts 1 and 3 by another route.
