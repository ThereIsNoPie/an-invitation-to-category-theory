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

**Why implication is forced, and what closure really asserts.**
$\mathsf{Bool}$ is the two-object category $\bot \leq \top$. Being *monoidal
closed* is not a single adjunction — it is one adjunction
$(-\land x) \dashv (x \multimap -)$ for **every** $x$. Bool has two elements,
so this is a family of exactly two adjunctions (blue = left adjoint
$-\land x$, red = right adjoint $x \multimap -$; dashed arrows show where each
element goes):

```svg
<svg viewBox="0 0 620 290" role="img" aria-label="Monoidal closure of Bool shown as a family of two adjunctions, one for x equals bottom giving constant maps and one for x equals top giving the identity">
  <line x1="310" y1="30" x2="310" y2="235" stroke="currentColor" stroke-width="1" stroke-opacity="0.25"/>

  <!-- ===== Group A: x = ⊥ ===== -->
  <text x="150" y="36" font-size="15" font-weight="bold" text-anchor="middle" fill="currentColor">x = ⊥</text>
  <text x="150" y="58" font-size="14" text-anchor="middle"><tspan fill="var(--agda-function)">(− ∧ ⊥)</tspan><tspan fill="currentColor"> ⊣ </tspan><tspan fill="var(--agda-type)">(⊥ ⊸ −)</tspan></text>

  <text x="40" y="105" font-size="14" text-anchor="middle" fill="currentColor">Bool</text>
  <text x="100" y="105" font-size="16" text-anchor="middle" fill="currentColor">⊥</text>
  <text x="200" y="105" font-size="16" text-anchor="middle" fill="currentColor">⊤</text>
  <line x1="116" y1="99" x2="184" y2="99" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <text x="40" y="215" font-size="14" text-anchor="middle" fill="currentColor">Bool</text>
  <text x="100" y="215" font-size="16" text-anchor="middle" fill="currentColor">⊥</text>
  <text x="200" y="215" font-size="16" text-anchor="middle" fill="currentColor">⊤</text>
  <line x1="116" y1="209" x2="184" y2="209" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <!-- left adjoint − ∧ ⊥ : both ↦ ⊥ -->
  <path d="M 92 110 C 78 136 78 166 92 194" fill="none" stroke="var(--agda-function)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 192 112 Q 118 182 108 192" fill="none" stroke="var(--agda-function)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <!-- right adjoint ⊥ ⊸ − : both ↦ ⊤ -->
  <path d="M 108 192 Q 182 120 192 112" fill="none" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 208 194 C 222 166 222 136 208 110" fill="none" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>

  <!-- ===== Group B: x = ⊤ ===== -->
  <text x="470" y="36" font-size="15" font-weight="bold" text-anchor="middle" fill="currentColor">x = ⊤</text>
  <text x="470" y="58" font-size="14" text-anchor="middle"><tspan fill="var(--agda-function)">(− ∧ ⊤)</tspan><tspan fill="currentColor"> ⊣ </tspan><tspan fill="var(--agda-type)">(⊤ ⊸ −)</tspan><tspan fill="currentColor"> = id ⊣ id</tspan></text>

  <text x="360" y="105" font-size="14" text-anchor="middle" fill="currentColor">Bool</text>
  <text x="420" y="105" font-size="16" text-anchor="middle" fill="currentColor">⊥</text>
  <text x="520" y="105" font-size="16" text-anchor="middle" fill="currentColor">⊤</text>
  <line x1="436" y1="99" x2="504" y2="99" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <text x="360" y="215" font-size="14" text-anchor="middle" fill="currentColor">Bool</text>
  <text x="420" y="215" font-size="16" text-anchor="middle" fill="currentColor">⊥</text>
  <text x="520" y="215" font-size="16" text-anchor="middle" fill="currentColor">⊤</text>
  <line x1="436" y1="209" x2="504" y2="209" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <!-- left adjoint − ∧ ⊤ = id : ⊥ ↦ ⊥, ⊤ ↦ ⊤ (offset left) -->
  <path d="M 412 110 L 412 194" fill="none" stroke="var(--agda-function)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 512 110 L 512 194" fill="none" stroke="var(--agda-function)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <!-- right adjoint ⊤ ⊸ − = id : ⊥ ↦ ⊥, ⊤ ↦ ⊤ (offset right) -->
  <path d="M 428 194 L 428 110" fill="none" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 528 194 L 528 110" fill="none" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>

  <text x="310" y="268" font-size="13" text-anchor="middle" fill="currentColor">monoidal closed = one adjunction (− ∧ x) ⊣ (x ⊸ −) for every x ∈ Bool</text>
</svg>
```

Within each column the left adjoint $(-\land x)$ has a *unique* right adjoint,
so once $\land$ is fixed there is no freedom left — forcing
$x \multimap y = \neg x \lor y$. Exercise 2.59 is precisely the per-$x$
equivalence: "closure condition at $x$" ⟺ "adjunction at $x$." Closure is that
whole family bundled together.

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
