---
layout: agda
title: "Bool with OR is Not Monoidal Closed"
section: "Examples"
chapter: 2
number: 62
---

# Bool with OR is Not Monoidal Closed

## Textbook Description

**Example 2.62.** A non-example is $(\mathbb{B}, \leq, \mathsf{false}, \lor)$. Indeed, suppose we had a $\multimap$ operator as in Definition 2.57. Note that $\mathsf{false} \leq p \multimap q$ for any $p, q$ no matter what $\multimap$ is, because $\mathsf{false}$ is less than everything.

But using $a = \mathsf{false}$, $p = \mathsf{true}$, and $q = \mathsf{false}$, we then get a contradiction: $(a \lor p) \not\leq q$ and yet $a \leq (p \multimap q)$.

## Agda Setup

```agda
module examples.chapter2.BoolOrNotClosed where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## The Ordering

We use the same ordering as before: false ≤ true.

```agda
data _≤𝔹_ : Bool → Bool → Set where
  ≤-refl : ∀ {x} → x ≤𝔹 x
  f≤t : false ≤𝔹 true
```

## The Contradiction

If (Bool, ≤, false, ∨) were monoidal closed, there would exist some operation ⊸ such that:

(a ∨ v) ≤ w iff a ≤ (v ⊸ w)

```agda
-- Assume a hypothetical ⊸ exists
module Contradiction (_⊸_ : Bool → Bool → Bool)
  (curry : ∀ {a v w} → (a ∨ v) ≤𝔹 w → a ≤𝔹 (v ⊸ w))
  (uncurry : ∀ {a v w} → a ≤𝔹 (v ⊸ w) → (a ∨ v) ≤𝔹 w)
  where

  -- false ≤ anything, so false ≤ (true ⊸ false)
  false≤hom : false ≤𝔹 (true ⊸ false)
  false≤hom with true ⊸ false
  ... | false = ≤-refl
  ... | true = f≤t

  -- By uncurry: false ≤ (true ⊸ false) implies (false ∨ true) ≤ false
  -- But (false ∨ true) = true, and true ≤ false is absurd!
  contradiction : ⊥
  contradiction with uncurry false≤hom
  ... | ()  -- true ≤ false has no proof
```

## Interpretation

The problem is that the ∨ operation is too "generous" - once you have true anywhere in the input, you get true. There's no way to define a hom-element that captures "the resources needed to convert $v$ to $w$" when the monoidal product is ∨.

In contrast, ∧ (AND) is "conservative" - you need both inputs to be true to get true. This makes it possible to define implication as the hom-element.

The deep reason is adjoint-theoretic. Closure at $x$ requires $(- \lor x)$ to have a right adjoint, and a map has a right adjoint only if it *preserves the bottom element* (the empty join). Now $(- \land x)$ sends $\mathsf{false} \mapsto \mathsf{false}$, so it can; but $(- \lor \mathsf{true})$ sends $\mathsf{false} \mapsto \mathsf{true}$, so it cannot. The contradiction above is exactly this failure made concrete: taking $x = \mathsf{true}$ picks out the one member of the would-be family of adjunctions that does not exist.
