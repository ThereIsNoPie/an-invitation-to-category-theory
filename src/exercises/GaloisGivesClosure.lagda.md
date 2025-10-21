---
layout: agda
title: "Galois Connection Gives Closure Operator"
section: "Exercises"
chapter: 1
number: 111
---

# Galois Connection Gives Closure Operator

## Textbook Exercise

**Exercise 1.111.** Suppose that f is left adjoint to g. Use Proposition 1.101 to show the following:

1. p ≤ (g ∘ f)(p)
2. (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p). To prove this, show inequalities in both directions, ≤ and ≥.

Given a Galois connection with f : P → Q left adjoint to g : Q → P, we may compose f and g to arrive at a monotone map g ∘ f : P → P from preorder P to itself. This monotone map has the property that p ≤ (g ∘ f)(p), and that (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p) for any p ∈ P. This is an example of a closure operator.

## Agda Setup

```agda
module exercises.GaloisGivesClosure where

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import definitions.Preorder using (Preorder)
open import definitions.GaloisConnection using (GaloisConnection)
open import definitions.ClosureOperator using (ClosureOperator)
open import definitions.MonotoneMap using (Monotonic)
open import propositions.GaloisUnitCounit using (galois→unit-counit)
```

## Problem

Given a Galois connection with f : P → Q left adjoint to g : Q → P, we construct a closure operator from the composition g ∘ f.

```agda
module _ (P Q : Preorder) (gc : GaloisConnection P Q) where
  open Preorder P renaming (Carrier to A; _≤_ to _≤P_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤Q_)
  open GaloisConnection gc

  -- Part 1: Show p ≤ (g ∘ f)(p)
  part1 : ∀ (p : A) → p ≤P g (f p)

  -- Part 2: Show (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p)
  part2 : ∀ (p : A) → (g (f (g (f p))) ≤P g (f p)) × (g (f p) ≤P g (f (g (f p))))

  -- Construct the closure operator g ∘ f : P → P
  galois-closure : ClosureOperator P
```

## Solution

**Strategy:** Use Proposition 1.101 (unit-counit form) to extract the unit and counit, then:
- Part 1 follows directly from the unit
- Part 2 uses g-monotonic with counit for forward, and unit applied to g(f(p)) for backward

```agda
  private
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

  -- Part 1: p ≤ (g ∘ f)(p) is exactly the unit condition
  part1 = unit

  -- Part 2: Show both directions of (g ∘ f ∘ g ∘ f)(p) ≅ (g ∘ f)(p)
  part2 p = (part2-forward p , part2-backward p)
    where
      -- Forward: g(f(g(f(p)))) ≤ g(f(p))
      -- Apply g-monotonic to the counit at f(p)
      part2-forward : ∀ (p : A) → g (f (g (f p))) ≤P g (f p)
      part2-forward p = beginP
        g (f (g (f p))) ≤P⟨ g-monotonic (counit (f p)) ⟩
        g (f p)         ∎P

      -- Backward: g(f(p)) ≤ g(f(g(f(p))))
      -- Apply the unit condition to g(f(p))
      part2-backward : ∀ (p : A) → g (f p) ≤P g (f (g (f p)))
      part2-backward p = beginP
        g (f p)         ≤P⟨ unit (g (f p)) ⟩
        g (f (g (f p))) ∎P

  -- Construct the closure operator
  galois-closure = record
    { j = j
    ; j-monotonic = j-monotonic
    ; extensive = part1
    ; idempotent = part2
    }
    where
      -- g ∘ f is monotonic (composition of monotonic functions)
      j-monotonic : Monotonic _≤P_ _≤P_ j
      j-monotonic {p₁} {p₂} p₁≤p₂ = g-monotonic (f-monotonic p₁≤p₂)
```
