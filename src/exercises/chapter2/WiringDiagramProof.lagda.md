---
layout: agda
title: "Wiring Diagram Formal Proof"
section: "Exercises"
chapter: 2
number: 10
---

# Exercise 2.10: Wiring Diagram Formal Proof

## Textbook Exercise

**Exercise 2.10.** The string of inequalities in Eq. (2.10) is not quite a proof, because technically there is no such thing as v + w + u, for example. Instead, there is (v + w) + u and v + (w + u), and so on.

1. Formally prove, using only the rules of symmetric monoidal preorders (Definition 2.1) that, given the assertions in Eq. (2.8), the conclusion in Eq. (2.9) follows.

2. Reflexivity and transitivity should show up in your proof. Make sure you are explicit about where they do.

3. How can you look at the wiring diagram (2.5) and know that the symmetry axiom (Definition 2.1(d)) does not need to be invoked?

**Context:** The inner boxes in diagram (2.7) translate into the assertions:
```text
t ≤ v + w,    w + u ≤ x + z,    v + x ≤ y    (2.8)
```
and the outer box translates into the assertion:
```text
t + u ≤ y + z    (2.9)
```
The informal proof is:
```text
t + u ≤ v + w + u ≤ v + x + z ≤ y + z    (2.10)
```

## Agda Setup

```agda
module exercises.chapter2.WiringDiagramProof where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder; SymmetricMonoidalStructure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import plumbing.EquationalReasoning as ER
```

## Problem

**Part 1:** Formalize and prove the theorem using only the axioms of symmetric monoidal preorders.

```agda
module _ (SMP : SymmetricMonoidalPreorder) where
  open SymmetricMonoidalPreorder SMP

  -- The formal proof that the outer box follows from the inner boxes
  wiring-diagram-proof :
    ∀ {t v w u x z y : Carrier} →
    -- Premises (2.8): the inner boxes
    t ≤ (v ⊗ w) →
    (w ⊗ u) ≤ (x ⊗ z) →
    (v ⊗ x) ≤ y →
    -- Conclusion (2.9): the outer box
    (t ⊗ u) ≤ (y ⊗ z)
```

## Solution

**Strategy:** We follow the chain of inequalities from Eq. (2.10), making explicit use of associativity to handle parenthesization, monotonicity to preserve inequalities through products, reflexivity for trivial inequalities, and transitivity to chain the steps together.

The key insight is that we need to:
1. Start with t ⊗ u
2. Use monotonicity with t ≤ v ⊗ w and u ≤ u (reflexivity) to get t ⊗ u ≤ (v ⊗ w) ⊗ u
3. Reassociate to v ⊗ (w ⊗ u) using associativity
4. Use monotonicity with w ⊗ u ≤ x ⊗ z to get v ⊗ (w ⊗ u) ≤ v ⊗ (x ⊗ z)
5. Reassociate to (v ⊗ x) ⊗ z
6. Use monotonicity with v ⊗ x ≤ y to get (v ⊗ x) ⊗ z ≤ y ⊗ z
7. Chain everything together with transitivity

```agda
  open ER.≤-≡-Reasoning _≤_ reflexive transitive

  wiring-diagram-proof {t} {v} {w} {u} {x} {z} {y} t≤v⊗w w⊗u≤x⊗z v⊗x≤y =
    begin
      -- Start with the left side of the goal
      (t ⊗ u)
    ≤⟨ monotonicity t≤v⊗w reflexive ⟩  -- REFLEXIVITY (u ≤ u)
      -- Use monotonicity: t ≤ v ⊗ w and u ≤ u implies t ⊗ u ≤ (v ⊗ w) ⊗ u
      ((v ⊗ w) ⊗ u)
    ≡⟨ associativity ⟩
      -- Reassociate using associativity
      (v ⊗ (w ⊗ u))
    ≤⟨ monotonicity reflexive w⊗u≤x⊗z ⟩  -- REFLEXIVITY (v ≤ v)
      -- Use monotonicity: v ≤ v and w ⊗ u ≤ x ⊗ z implies v ⊗ (w ⊗ u) ≤ v ⊗ (x ⊗ z)
      (v ⊗ (x ⊗ z))
    ≡˘⟨ associativity ⟩
      -- Reassociate using associativity (backward)
      ((v ⊗ x) ⊗ z)
    ≤⟨ monotonicity v⊗x≤y reflexive ⟩  -- REFLEXIVITY (z ≤ z)
      -- Use monotonicity: v ⊗ x ≤ y and z ≤ z implies (v ⊗ x) ⊗ z ≤ y ⊗ z
      (y ⊗ z)
    ∎
      -- The chain is complete, and TRANSITIVITY is implicit in the reasoning chain
```

## Part 2: Reflexivity and Transitivity

**Reflexivity** appears explicitly in three places in the equational reasoning chain:

1. Line 85: `monotonicity t≤v⊗w reflexive` - uses `reflexive` to prove u ≤ u
2. Line 91: `monotonicity reflexive w⊗u≤x⊗z` - uses `reflexive` to prove v ≤ v
3. Line 97: `monotonicity v⊗x≤y reflexive` - uses `reflexive` to prove z ≤ z

Each of these applications of reflexivity is necessary to apply the monotonicity axiom, which requires proofs that both arguments are related by ≤.

**Transitivity** appears implicitly throughout the equational reasoning chain. Each step in the chain:
```text
(t ⊗ u) ≤⟨ ... ⟩ ((v ⊗ w) ⊗ u) ≤⟨ ... ⟩ ... ≤⟨ ... ⟩ (y ⊗ z)
```
uses transitivity to combine the individual inequality steps. The `≤-≡-Reasoning` module's `_≤⟨_⟩_` operator explicitly calls `transitive` to chain each step with the next. The final `∎` operator uses reflexivity to conclude the chain.

So while the proof reads as a linear chain of steps, it is actually building up nested applications of transitivity behind the scenes, just as in the original proof.

## Part 3: Why Symmetry Is Not Needed

**Answer:** By examining the wiring diagram (2.5), we can see that no wires cross each other. The symmetry axiom x ⊗ y = y ⊗ x corresponds to swapping or crossing wires in the diagram. Since all wires in diagram (2.7) flow from left to right without any crossings or swaps, we never need to exchange the order of elements in a tensor product, and thus the symmetry axiom is not invoked.

More formally: the proof only requires transformations that preserve the left-to-right order of variables. We use:
- Monotonicity (vertical composition of boxes)
- Associativity (regrouping without reordering)
- Reflexivity and transitivity (basic preorder reasoning)

None of these require swapping the order of tensor products, which is what symmetry provides.