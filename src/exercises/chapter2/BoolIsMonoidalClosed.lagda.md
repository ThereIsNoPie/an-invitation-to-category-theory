---
layout: agda
title: "Bool is Monoidal Closed"
section: "Exercises"
chapter: 2
number: 61
---

# Bool is Monoidal Closed

## Textbook Exercise

**Exercise 2.61.** Show that $\mathsf{Bool} = (\mathbb{B}, \leq, \mathsf{true}, \land)$ is monoidal closed.

## Agda Setup

```agda
module exercises.chapter2.BoolIsMonoidalClosed where

open import definitions.chapter2.MonoidalClosed
  using (IsMonoidalClosed; MonoidalClosedPreorder)
open import examples.chapter2.BoolAnd using (Bool-SMP; _≤𝔹_; ≤-refl; f≤t)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
```

## Problem

Find a hom-element $x \multimap y$ in $\mathbb{B}$ satisfying the closure
condition $(a \land x) \leq y \iff a \leq (x \multimap y)$.

```agda
Bool-closed : IsMonoidalClosed Bool-SMP

Bool-MCP : MonoidalClosedPreorder
```

## Solution

The hom-element in Bool is implication: $x \multimap y = \neg x \lor y$, which is equivalent to $x \Rightarrow y$.

The closure condition $(a \land x) \leq y \Leftrightarrow a \leq (x \multimap y)$ becomes:
- $(a \land x) \leq y$ means "if $a$ and $x$ are both true, then $y$ is true"
- $a \leq (x \Rightarrow y)$ means "if $a$ is true, then $x$ implies $y$"

These are equivalent by the standard logical equivalence: $(a \land x) \Rightarrow y \Leftrightarrow a \Rightarrow (x \Rightarrow y)$.

```agda
-- Boolean implication: x ⊸ y = ¬x ∨ y = x → y
_⊸𝔹_ : Bool → Bool → Bool
x ⊸𝔹 y = not x ∨ y

-- Helper: false ≤ anything
false≤any : ∀ {b} → false ≤𝔹 b
false≤any {false} = ≤-refl
false≤any {true} = f≤t

-- (a ∧ x) ≤ y iff a ≤ (x ⊸ y): check all the relevant cases

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

Bool-closed = record
  { _⊸_ = _⊸𝔹_
  ; curry = Bool-curry
  ; uncurry = Bool-uncurry
  }

Bool-MCP = record
  { base = Bool-SMP
  ; closed = Bool-closed
  }
```

## Interpretation

The monoidal closed structure of Bool captures the logical relationship between conjunction and implication. The fact that $\land$ has a right adjoint $\Rightarrow$ is the fundamental property underlying the deduction theorem in propositional logic.
