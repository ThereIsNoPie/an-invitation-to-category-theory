---
layout: agda
title: "Bool is a Quantale"
section: "Exercises"
chapter: 2
number: 69
---

# Bool is a Quantale

## Textbook Exercise

**Exercise 2.69.** Show that $\mathbf{Bool} = (\mathbb{B}, \leq, \mathsf{true}, \wedge)$ is a quantale.

## Agda Setup

```agda
module exercises.chapter2.BoolIsQuantale where

open import definitions.chapter2.Quantale using (Quantale; HasAllJoins)
open import exercises.chapter2.BoolIsMonoidalClosed using (Bool-MCP)
open import examples.chapter2.BoolAnd using (Bool-SMP; _≤𝔹_; ≤-refl; f≤t)
open import plumbing.ClassicalPostulates using (LEM)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
```

## Problem

Bool is already monoidal closed (Exercise 2.61). It remains to show it has all
joins. The general join of a family $a : \text{Idx} \to \mathbb{B}$ is
"existential OR": $\bigvee a = \mathsf{true}$ iff $\exists\, i,\ a(i) = \mathsf{true}$.
Deciding this existential for an arbitrary index set requires classical logic.

```agda
-- The general join: true iff some a(i) is true
⋁-Bool : {Idx : Set} → (Idx → Bool) → Bool

Bool-has-joins : HasAllJoins Bool-SMP

Bool-Quantale : Quantale
```

## Solution

```agda
⋁-Bool {Idx} a with LEM {P = ∃ λ i → a i ≡ true}
... | inj₁ _ = true
... | inj₂ _ = false

-- Helper: any Bool is ≤ true
private
  ≤-true : ∀ b → b ≤𝔹 true
  ≤-true false = f≤t
  ≤-true true  = ≤-refl

  false-≤ : ∀ b → false ≤𝔹 b
  false-≤ false = ≤-refl
  false-≤ true  = f≤t

  not-true→false : ∀ {b} → (b ≡ true → ⊥) → b ≡ false
  not-true→false {false} _ = refl
  not-true→false {true}  h = ⊥-elim (h refl)

Bool-has-joins = record
  { ⋁       = ⋁-Bool
  ; join-ub  = λ {Idx} {a} {i} → go {Idx} {a} {i}
  ; join-lub = λ {Idx} {a} {b} → lub {Idx} {a} {b}
  }
  where
    -- a i ≤ ⋁ a: if any witness exists, ⋁ a = true so a i ≤ true;
    --            otherwise ⋁ a = false, and a i must also be false (else contradiction)
    go : {Idx : Set} {a : Idx → Bool} {i : Idx} → a i ≤𝔹 ⋁-Bool a
    go {Idx} {a} {i} with LEM {P = ∃ λ j → a j ≡ true}
    ... | inj₁ _  = ≤-true (a i)
    ... | inj₂ no = subst (_≤𝔹 false) (sym (not-true→false (λ eq → no (i , eq)))) ≤-refl

    -- (∀ i → a i ≤ b) → ⋁ a ≤ b: if some a i = true then b = true (from the hypothesis);
    --                              otherwise ⋁ a = false ≤ b
    lub : {Idx : Set} {a : Idx → Bool} {b : Bool}
        → (∀ i → a i ≤𝔹 b) → ⋁-Bool a ≤𝔹 b
    lub {Idx} {a} {b} h with LEM {P = ∃ λ i → a i ≡ true}
    ... | inj₁ (i , ai≡true) = subst (_≤𝔹 b) ai≡true (h i)
    ... | inj₂ _              = false-≤ b

Bool-Quantale = record
  { closedPreorder = Bool-MCP
  ; hasAllJoins    = Bool-has-joins
  }
```

## Interpretation

The general join in Bool is existential: $\bigvee a = \mathsf{true}$ iff some
$a(i)$ is true. The two cases from Exercise 2.68 follow immediately: the empty
join ($\text{Idx} = \bot$, no witnesses) is $\mathsf{false}$, and the binary
join ($\text{Idx} = \mathbb{B}$, two candidates) is logical OR.

Classical logic is needed because for an arbitrary set $\text{Idx}$ there is no
way to computationally search for a witness — but classically, either one exists
or it doesn't.
