---
layout: agda
title: "Bool is Monoidal Closed"
section: "Exercises"
chapter: 2
number: 61
---

# Bool is Monoidal Closed

## Textbook Description

**Exercise 2.58.** Show that $\mathsf{Bool} = (\mathbb{B}, \leq, \mathsf{true}, \land)$ is monoidal closed.

## Solution

The hom-element in Bool is implication: $x \multimap y = \neg x \lor y$, which is equivalent to $x \Rightarrow y$.

The closure condition $(a \land x) \leq y \Leftrightarrow a \leq (x \multimap y)$ becomes:
- $(a \land x) \leq y$ means "if $a$ and $x$ are both true, then $y$ is true"
- $a \leq (x \Rightarrow y)$ means "if $a$ is true, then $x$ implies $y$"

These are equivalent by the standard logical equivalence: $(a \land x) \Rightarrow y \Leftrightarrow a \Rightarrow (x \Rightarrow y)$.

## Agda Setup

```agda
module exercises.chapter2.BoolIsMonoidalClosed where

open import definitions.chapter2.MonoidalClosed
  using (IsMonoidalClosed; MonoidalClosedPreorder)
open import examples.chapter2.BoolAnd using (Bool-SMP; _≤𝔹_; ≤-refl)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Product using (_,_)
```

## The Hom-Element (Implication)

```agda
-- Boolean implication: x ⊸ y = ¬x ∨ y = x → y
_⊸𝔹_ : Bool → Bool → Bool
x ⊸𝔹 y = not x ∨ y
  where
    _∨_ : Bool → Bool → Bool
    false ∨ b = b
    true ∨ _ = true
```

## The Closure Property

```agda
-- Helper: false ≤ anything
false≤any : ∀ {b} → false ≤𝔹 b
false≤any {false} = ≤-refl
false≤any {true} = f≤t
  where open _≤𝔹_

-- (a ∧ x) ≤ y iff a ≤ (x ⊸ y)
-- In Bool: if (a ∧ x) implies y, then a implies (x implies y)

Bool-curry : ∀ {a x y} → (a ∧ x) ≤𝔹 y → a ≤𝔹 (x ⊸𝔹 y)
Bool-curry {false} {_} {_} _ = false≤any
Bool-curry {true} {false} {_} _ = ≤-refl  -- true ≤ (false ⊸ y) = true ≤ true
Bool-curry {true} {true} {false} ()       -- (true ∧ true) ≤ false is impossible
Bool-curry {true} {true} {true} _ = ≤-refl

Bool-uncurry : ∀ {a x y} → a ≤𝔹 (x ⊸𝔹 y) → (a ∧ x) ≤𝔹 y
Bool-uncurry {false} {_} {_} _ = false≤any
Bool-uncurry {true} {false} {_} _ = false≤any  -- (true ∧ false) = false ≤ y
Bool-uncurry {true} {true} {false} ()          -- true ≤ (true ⊸ false) = true ≤ false impossible
Bool-uncurry {true} {true} {true} _ = ≤-refl
```

## Bool as Monoidal Closed

```agda
Bool-closed : IsMonoidalClosed Bool-SMP
Bool-closed = record
  { _⊸_ = _⊸𝔹_
  ; curry = Bool-curry
  ; uncurry = Bool-uncurry
  }

Bool-MCP : MonoidalClosedPreorder
Bool-MCP = record
  { base = Bool-SMP
  ; closed = Bool-closed
  }
```

## Interpretation

The monoidal closed structure of Bool captures the logical relationship between conjunction and implication. The fact that $\land$ has a right adjoint $\Rightarrow$ is the fundamental property underlying the deduction theorem in propositional logic.
