---
layout: agda
title: "Closure Adjunction Example"
section: "Exercises"
chapter: 1
number: 117
---

# Closure Adjunction Example

## Textbook Exercise

**Exercise 1.117.** Let S = {1, 2, 3}. Let's try to understand the adjunction discussed above.

1. Come up with any preorder relation ≤ on S, and define U(≤) to be the subset U(≤) := {(s₁, s₂) | s₁ ≤ s₂} ⊆ S × S, i.e. U(≤) is the image of ≤ under the inclusion Pos(S) → Rel(S), the relation "underlying" the preorder.

2. Come up with any two binary relations Q ⊆ S × S and Q' ⊆ S × S such that Q ⊆ U(≤) but Q' ⊈ U(≤). Note that your choice of Q, Q' do not have to come from preorders.

We now want to check that, in this case, the closure operation Cl is really left adjoint to the "underlying relation" map U.

3. Concretely (without using the assertion that there is some sort of adjunction), show that Cl(Q) ⊑ ≤, where ⊑ is the order on Pos(S), defined immediately above this exercise.

4. Concretely show that Cl(Q') ⊈ ≤.

## Context

For any set S, there is a set Pos(S) consisting of all preorder relations on S. There is a preorder structure ⊑ on Pos(S) given by inclusion: ≤₁ ⊑ ≤₂ if (a ≤₁ b → a ≤₂ b) for every a, b ∈ S.

Every preorder relation is a relation, so we have an inclusion U : Pos(S) → Rel(S). This is the right adjoint of a Galois connection. Its left adjoint is Cl : Rel(S) → Pos(S), which takes the reflexive and transitive closure of a relation.

## Agda Setup

```agda
module exercises.ClosureAdjunctionExample where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)

open import definitions.Relation using (BinRel)
open import definitions.Preorder using (IsPreorder)

-- Our set S = {1, 2, 3}
S : Set
S = Fin 3

-- Pattern synonyms for readability
pattern s₁ = zero
pattern s₂ = suc zero
pattern s₃ = suc (suc zero)
```

## Problem

We'll work with S = {1, 2, 3} and demonstrate the Galois connection Cl ⊣ U.

```agda
-- Reflexive-transitive closure of a relation
data Cl (R : BinRel S) : BinRel S where
  incl  : ∀ {a b} → R a b → Cl R a b           -- Include original relation
  refl  : ∀ {a} → Cl R a a                     -- Reflexivity
  trans : ∀ {a b c} → Cl R a b → Cl R b c → Cl R a c  -- Transitivity

module Exercise where
  -- Part 1: Define a preorder relation on S
  _≤_ : BinRel S
  ≤-isPreorder : IsPreorder _≤_

  -- Part 2: Define relations Q and Q'
  Q : BinRel S                                   -- Q ⊆ U(≤)
  Q⊆U : ∀ {a b} → Q a b → a ≤ b

  Q' : BinRel S                                  -- Q' ⊈ U(≤)
  Q'⊈U-witness-a : S
  Q'⊈U-witness-b : S
  Q'⊈U-holds : Q' Q'⊈U-witness-a Q'⊈U-witness-b
  Q'⊈U-fails : ¬ (Q'⊈U-witness-a ≤ Q'⊈U-witness-b)

  -- Part 3: Show Cl(Q) ⊑ ≤
  Cl-Q-isPreorder : IsPreorder (Cl Q)
  Cl-Q⊑≤ : ∀ {a b} → Cl Q a b → a ≤ b

  -- Part 4: Show Cl(Q') ⊈ ≤
  Cl-Q'⊈≤-witness-a : S
  Cl-Q'⊈≤-witness-b : S
  Cl-Q'⊈≤-holds : Cl Q' Cl-Q'⊈≤-witness-a Cl-Q'⊈≤-witness-b
  Cl-Q'⊈≤-fails : ¬ (Cl-Q'⊈≤-witness-a ≤ Cl-Q'⊈≤-witness-b)
```

## Solution

**Strategy:** We'll use a concrete example with S = {1, 2, 3}:
- Choose ≤ to be the standard order: 1 ≤ 1, 1 ≤ 2, 1 ≤ 3, 2 ≤ 2, 2 ≤ 3, 3 ≤ 3
- Choose Q to be a subset: just {(1,2), (2,3)}
- Choose Q' to contain something incompatible: {(2,1)}

```agda
  -- Part 1: Standard order on {1, 2, 3}: 1 ≤ 2 ≤ 3
  _≤_ s₁ s₁ = ⊤
  _≤_ s₁ s₂ = ⊤
  _≤_ s₁ s₃ = ⊤
  _≤_ s₂ s₁ = ⊥
  _≤_ s₂ s₂ = ⊤
  _≤_ s₂ s₃ = ⊤
  _≤_ s₃ s₁ = ⊥
  _≤_ s₃ s₂ = ⊥
  _≤_ s₃ s₃ = ⊤

  -- Prove reflexivity
  ≤-refl : ∀ {a} → a ≤ a
  ≤-refl {s₁} = tt
  ≤-refl {s₂} = tt
  ≤-refl {s₃} = tt

  -- Prove transitivity
  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans {s₁} {s₁} {s₁} _ _ = tt
  ≤-trans {s₁} {s₁} {s₂} _ _ = tt
  ≤-trans {s₁} {s₁} {s₃} _ _ = tt
  ≤-trans {s₁} {s₂} {s₂} _ _ = tt
  ≤-trans {s₁} {s₂} {s₃} _ _ = tt
  ≤-trans {s₁} {s₃} {s₃} _ _ = tt
  ≤-trans {s₂} {s₂} {s₂} _ _ = tt
  ≤-trans {s₂} {s₂} {s₃} _ _ = tt
  ≤-trans {s₂} {s₃} {s₃} _ _ = tt
  ≤-trans {s₃} {s₃} {s₃} _ _ = tt

  ≤-isPreorder = record
    { reflexive = ≤-refl
    ; transitive = ≤-trans
    }

  -- Part 2: Q contains only (1,2) and (2,3) - both are in ≤
  Q s₁ s₂ = ⊤
  Q s₂ s₃ = ⊤
  Q _  _  = ⊥

  -- Proof that Q ⊆ U(≤)
  Q⊆U {s₁} {s₂} _ = tt
  Q⊆U {s₂} {s₃} _ = tt

  -- Q' contains (2,1) which is NOT in ≤ (since 2 ≰ 1)
  Q' s₂ s₁ = ⊤
  Q' _  _  = ⊥

  -- Witnesses for Q' ⊈ U(≤)
  Q'⊈U-witness-a = s₂
  Q'⊈U-witness-b = s₁
  Q'⊈U-holds = tt
  Q'⊈U-fails ()

  -- Part 3: Cl(Q) is a preorder
  Cl-Q-isPreorder = record
    { reflexive = refl
    ; transitive = trans
    }

  -- Show Cl(Q) ⊑ ≤ by induction on the closure construction
  -- Since Q ⊆ ≤ and ≤ is already reflexive and transitive,
  -- any element built from Q via refl/trans is also in ≤
  Cl-Q⊑≤ (incl q) = Q⊆U q              -- Q a b implies a ≤ b
  Cl-Q⊑≤ refl = ≤-refl                 -- ≤ is reflexive
  Cl-Q⊑≤ (trans p₁ p₂) = ≤-trans (Cl-Q⊑≤ p₁) (Cl-Q⊑≤ p₂)  -- ≤ is transitive

  -- Part 4: We can show Cl(Q') s₂ s₁ holds (since Q' s₂ s₁ holds)
  -- but s₂ ≤ s₁ does not hold
  Cl-Q'⊈≤-witness-a = s₂
  Cl-Q'⊈≤-witness-b = s₁
  Cl-Q'⊈≤-holds = incl tt
  Cl-Q'⊈≤-fails ()
```

## Summary

This exercise demonstrates the Galois connection Cl ⊣ U:

- **Part 3** shows that when Q ⊆ U(≤), we have Cl(Q) ⊑ ≤. This verifies one direction of the adjunction: if the left adjoint applied to Q is below ≤, then Q must be below the right adjoint of ≤.

- **Part 4** shows that when Q' ⊈ U(≤), we have Cl(Q') ⊈ ≤. This demonstrates that the adjunction relationship genuinely depends on the subset inclusion.

Together, these illustrate the adjunction property: Cl(R) ⊑ P if and only if R ⊆ U(P).
```
