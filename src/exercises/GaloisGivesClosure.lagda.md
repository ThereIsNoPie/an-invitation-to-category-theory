---
layout: agda
title: "Galois Connection Gives Closure Operator"
section: "Exercises"
chapter: 1
number: 111
---

# Galois Connection Gives Closure Operator

**Exercise 1.111.** Suppose that f is left adjoint to g. Use Proposition 1.101 to show the following:

1. p ≤ (g ∘ f)(p)
2. (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p). To prove this, show inequalities in both directions, ≤ and ≥.

## Context

Given a Galois connection with f : P → Q left adjoint to g : Q → P, we may compose f and g to arrive at a monotone map g ∘ f : P → P from preorder P to itself. This monotone map has the property that p ≤ (g ∘ f)(p), and that (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p) for any p ∈ P. This is an example of a closure operator.

## Setup

```agda
module exercises.GaloisGivesClosure where

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import definitions.Preorder using (Preorder)
open import definitions.GaloisConnection using (GaloisConnection)
open import definitions.ClosureOperator using (ClosureOperator)
open import definitions.MonotoneMap using (Monotonic)
open import propositions.GaloisUnitCounit using (galois→unit-counit)
```

## Solution

```agda
module Solution (P Q : Preorder) (gc : GaloisConnection P Q) where
  open Preorder P renaming (Carrier to A; _≤_ to _≤P_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤Q_)
  open GaloisConnection gc
  open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
  open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

  -- The composition g ∘ f
  j : A → A
  j p = g (f p)

  -- Extract unit and counit from Proposition 1.101
  unit : ∀ (p : A) → p ≤P g (f p)
  unit = proj₁ (galois→unit-counit P Q gc)

  counit : ∀ (q : B) → f (g q) ≤Q q
  counit = proj₂ (galois→unit-counit P Q gc)
```

### Part 1: p ≤ (g ∘ f)(p)

This is exactly the unit condition from Proposition 1.101.

```agda
  -- Part 1: p ≤ (g ∘ f)(p)
  part1 : ∀ (p : A) → p ≤P j p
  part1 = unit
```

### Part 2: (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p)

We need to show both directions of the equivalence.

**Forward direction:** (g ∘ f ∘ g ∘ f)(p) ≤ (g ∘ f)(p)

**Strategy:** Apply g-monotonic to the counit at f(p).

```agda
  -- Forward: g(f(g(f(p)))) ≤ g(f(p))
  part2-forward : ∀ (p : A) → j (j p) ≤P j p
  part2-forward p = beginP
    g (f (g (f p))) ≤P⟨ g-monotonic (counit (f p)) ⟩
    g (f p)         ∎P
```

**Backward direction:** (g ∘ f)(p) ≤ (g ∘ f ∘ g ∘ f)(p)

**Strategy:** Apply the unit condition to g(f(p)).

```agda
  -- Backward: g(f(p)) ≤ g(f(g(f(p))))
  part2-backward : ∀ (p : A) → j p ≤P j (j p)
  part2-backward p = beginP
    g (f p)         ≤P⟨ unit (g (f p)) ⟩
    g (f (g (f p))) ∎P
```

**Combining both directions:**

```agda
  -- Part 2: (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p)
  part2 : ∀ (p : A) → (j (j p) ≤P j p) × (j p ≤P j (j p))
  part2 p = (part2-forward p , part2-backward p)
```

## Constructing the Closure Operator

Now we can construct the closure operator g ∘ f : P → P.

```agda
  -- g ∘ f is monotonic (composition of monotonic functions)
  j-monotonic : Monotonic _≤P_ _≤P_ j
  j-monotonic {p₁} {p₂} p₁≤p₂ = g-monotonic (f-monotonic p₁≤p₂)

  -- The closure operator
  galois-closure : ClosureOperator P
  galois-closure = record
    { j = j
    ; j-monotonic = j-monotonic
    ; extensive = part1
    ; idempotent = part2
    }
```

## Interpretation

This exercise shows that **every Galois connection gives rise to a closure operator** via the composition g ∘ f. The key insights are:

- **Extensivity** (p ≤ g(f(p))) comes directly from the unit condition
- **Idempotence** (g(f(g(f(p)))) ≅ g(f(p))) follows from applying the unit and counit conditions
- **Monotonicity** is automatic from the fact that both f and g are monotonic

Together with Example 1.114 (which shows the converse - every closure operator gives a Galois connection), this establishes a fundamental correspondence between Galois connections and closure operators.
```
