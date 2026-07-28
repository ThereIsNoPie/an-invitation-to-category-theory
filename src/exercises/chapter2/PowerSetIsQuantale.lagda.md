---
layout: agda
title: "Power Set is a Quantale"
section: "Exercises"
chapter: 2
number: 70
---

# Power Set is a Quantale

## Textbook Exercise

**Exercise 2.70.** Let $S$ be a set and recall the power set monoidal preorder
$(P(S), \subseteq, S, \cap)$ from Exercise 2.19. Is it a quantale?

## Agda Setup

```agda
module exercises.chapter2.PowerSetIsQuantale where

open import exercises.chapter2.PowerSetIntersection
  using (PowerSet; _⊆'_; _∩_; FullSet)
open import Data.Product using (∃; _,_)
```

## Problem

$(P(S), \subseteq, S, \cap)$ is a quantale. Exercise 2.19 gives the symmetric
monoidal preorder structure. It remains to exhibit the internal hom and the
general join.

**Internal hom:** membership in $A \multimap B$ is pointwise implication —
$x \in (A \multimap B)$ iff $x \in A$ implies $x \in B$.

**Join:** the join of a family of subsets is their union —
$x \in \bigvee_i A_i$ iff $\exists\, i,\ x \in A_i$. Unlike Bool, this is
*constructive*: to join, you pair the element with the index that witnesses
its membership.

```agda
-- Internal hom: pointwise implication
_⊸_ : {S : Set} → PowerSet S → PowerSet S → PowerSet S
(A ⊸ B) x = A x → B x

-- Closure: (A ∩ C ⊆ B) ↔ (C ⊆ A ⊸ B)
PS-curry   : {S : Set} {A B C : PowerSet S} → (A ∩ C) ⊆' B → C ⊆' (A ⊸ B)
PS-uncurry : {S : Set} {A B C : PowerSet S} → C ⊆' (A ⊸ B) → (A ∩ C) ⊆' B

-- Join: existential union
⋁-PS : {S : Set} {Idx : Set} → (Idx → PowerSet S) → PowerSet S

PS-join-ub  : {S : Set} {Idx : Set} {a : Idx → PowerSet S} {i : Idx}
            → a i ⊆' ⋁-PS a
PS-join-lub : {S : Set} {Idx : Set} {a : Idx → PowerSet S} {B : PowerSet S}
            → (∀ i → a i ⊆' B) → ⋁-PS a ⊆' B
```

## Solution

```agda
-- Closure is currying at the level of propositions
PS-curry   h cx ax     = h (ax , cx)
PS-uncurry h (ax , cx) = h cx ax

-- Union: the witness i and proof of membership travel together
⋁-PS a x = ∃ λ i → a i x

PS-join-ub  {i = i} aix     = i , aix
PS-join-lub h       (i , aix) = h i aix
```

## Interpretation

The powerset quantale has a pleasing structure:

- **⊗ = ∩** (intersection), **I = S** (full set) — the unit is the top element
- **⊸ = →** pointwise (logical implication on membership)
- **⋁ = ∃** pointwise (existential union)
- **𝟘 = ∅** (empty join, since no index witnesses membership in ∅)

All proofs are one-liners because the operations exactly match the logical
connectives. This is the Curry–Howard correspondence: the powerset quantale
*is* propositional logic, with subsets as propositions.

Contrast with Bool: Bool also has a join (OR), but proving it satisfies `HasAllJoins`
for arbitrary index sets required LEM. Here, the existential union is constructive
— no classical logic needed.

**Note on universe levels.** Because `PowerSet S = S → Set` lives in `Set₁`,
the full Quantale record (which expects a `Set`-level carrier) cannot directly
accommodate it. The ingredients above are all proved; wiring them into a
`Quantale` record would require a universe-polymorphic version of the definition.
