---
layout: agda
title: "Equational Reasoning"
section: "Plumbing"
---

# Equational Reasoning

This module provides syntax for **equational reasoning** with different relations. Instead of writing nested function applications, you can write chain-of-reasoning proofs that read like mathematical prose.

## For Equivalence Relations

Given an equivalence relation `∼`, you can write:
```text
begin
  a ∼⟨ proof-a∼b ⟩
  b ∼⟨ proof-b∼c ⟩
  c ∎
```

Instead of: `transitive proof-a∼b proof-b∼c`

## For Preorder Relations

Given a preorder `≤`, you can write:
```text
begin
  x ≤⟨ proof-x≤y ⟩
  y ≤⟨ proof-y≤z ⟩
  z ∎
```

Instead of: `transitive proof-x≤y proof-y≤z`

---

```agda
module plumbing.EquationalReasoning where

open import Relation.Binary.PropositionalEquality using (_≡_)
```

## Reasoning for Equivalence Relations

```agda
module ∼-Reasoning
  {A : Set}
  (_∼_ : A → A → Set)
  (reflexive : ∀ {x} → x ∼ x)
  (symmetric : ∀ {x y} → x ∼ y → y ∼ x)
  (transitive : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z)
  where

  infix  3 _∎
  infixr 2 _∼⟨_⟩_ _≈⟨_⟩_
  infix  1 begin_

  -- Start a reasoning chain
  begin_ : ∀ {x y} → x ∼ y → x ∼ y
  begin p = p

  -- Step forward: x ∼ y and y ∼ z implies x ∼ z
  _∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y ∼ z → x ∼ z
  x ∼⟨ p ⟩ q = transitive p q

  -- Alternative syntax with ≈ symbol (same as ∼)
  _≈⟨_⟩_ : ∀ x {y z} → x ∼ y → y ∼ z → x ∼ z
  x ≈⟨ p ⟩ q = transitive p q

  -- End a reasoning chain
  _∎ : ∀ x → x ∼ x
  x ∎ = reflexive

  -- Backward step: x ∼ y follows from y ∼ x by symmetry
  _∼˘⟨_⟩_ : ∀ x {y z} → y ∼ x → y ∼ z → x ∼ z
  x ∼˘⟨ p ⟩ q = transitive (symmetric p) q
```

## Reasoning for Preorder Relations

```agda
module ≤-Reasoning
  {A : Set}
  (_≤_ : A → A → Set)
  (reflexive : ∀ {x} → x ≤ x)
  (transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
  where

  infix  3 _∎
  infixr 2 _≤⟨_⟩_
  infix  1 begin_

  -- Start a reasoning chain
  begin_ : ∀ {x y} → x ≤ y → x ≤ y
  begin p = p

  -- Step forward: x ≤ y and y ≤ z implies x ≤ z
  _≤⟨_⟩_ : ∀ x {y z} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ p ⟩ q = transitive p q

  -- End a reasoning chain
  _∎ : ∀ x → x ≤ x
  x ∎ = reflexive
```

## Mixed Reasoning for Preorders with Equality

For proofs that mix preorder steps (≤) with equality steps (≡), such as when using associativity or other structural equalities:

```agda
module ≤-≡-Reasoning
  {A : Set}
  (_≤_ : A → A → Set)
  (reflexive : ∀ {x} → x ≤ x)
  (transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
  where

  open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

  infix  3 _∎
  infixr 2 _≤⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  1 begin_

  -- Start a reasoning chain
  begin_ : ∀ {x y} → x ≤ y → x ≤ y
  begin p = p

  -- Preorder step: x ≤ y and y ≤ z implies x ≤ z
  _≤⟨_⟩_ : ∀ x {y z} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ p ⟩ q = transitive p q

  -- Equality step (forward): x ≡ y and y ≤ z implies x ≤ z
  _≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y ≤ z → x ≤ z
  x ≡⟨ p ⟩ q = subst (λ expr → expr ≤ _) (sym p) q

  -- Equality step (backward): y ≡ x and y ≤ z implies x ≤ z
  _≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y ≤ z → x ≤ z
  x ≡˘⟨ p ⟩ q = subst (λ expr → expr ≤ _) p q

  -- End a reasoning chain
  _∎ : ∀ x → x ≤ x
  x ∎ = reflexive
```

## Reasoning for Propositional Equality

For completeness, we also provide reasoning for `≡` (though Agda's standard library has this).

```agda
module ≡-Reasoning where
  open import Relation.Binary.PropositionalEquality using (trans; sym; refl)

  infix  3 _∎
  infixr 2 _≡⟨_⟩_ _≡˘⟨_⟩_
  infix  1 begin_

  -- Start a reasoning chain
  begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
  begin p = p

  -- Step forward: x ≡ y and y ≡ z implies x ≡ z
  _≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = trans p q

  -- Backward step: x ≡ y follows from y ≡ x by symmetry
  _≡˘⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
  x ≡˘⟨ p ⟩ q = trans (sym p) q

  -- End a reasoning chain
  _∎ : ∀ {A : Set} (x : A) → x ≡ x
  x ∎ = refl
```

## Goal-Directed Reasoning

Equational reasoning chains steps **within one relation**: the lines are carrier
elements (`a`, `b`, `c`) and every step is a proof of `_≤_`/`_∼_`/`_≡_` between
adjacent lines. It cannot express a step that changes the *shape* of the whole
judgement — e.g. transposing `(a ⊗ v) ≤ w` into `a ≤ (v ⊸ w)` across an
adjunction.

**Goal-directed reasoning** works one level up. Each line is a whole *statement*
(a type), and each step is an arbitrary function between statements. You read it
top-down, starting from the goal:

```text
Goal            by f ⟵      -- to prove Goal, apply f to a proof of the next line
NextStatement   by g ⟵      -- to prove that, apply g to a proof of the next line
BaseStatement   witness s   -- the base case: s is a proof of BaseStatement
```

producing `f (g s)` — but with every intermediate statement spelled out and
checked by Agda. Because the steps are ordinary functions, a `witness` (or any
step) may itself contain a `begin … ∎` chain: that is how you combine the two
styles — goal-directed for the shape-changing steps, equational reasoning for the
composition chains nested inside.

```agda
module Goal-Reasoning where

  infixr 1 _by_⟵_
  infix  2 _witness_

  -- Reduce the goal T to a subgoal S via f : S → T
  _by_⟵_ : (T : Set) {S : Set} → (S → T) → S → T
  (T by f ⟵ s) = f s

  -- Discharge the final statement S with a proof s : S (spelling out S)
  _witness_ : (S : Set) → S → S
  (S witness s) = s
```

## Examples

Here are some example usages:

```agda
module Examples where
  open import definitions.chapter1.EquivalenceRelation using (IsEquivalence)
  open import definitions.chapter1.Relation using (BinRel)

  -- Example: Using ∼-Reasoning
  module EquivExample
    {A : Set}
    (_∼_ : BinRel A)
    (equiv : IsEquivalence _∼_)
    where

    open IsEquivalence equiv
    open ∼-Reasoning _∼_ reflexive symmetric transitive

    -- Instead of: transitive (transitive a∼b b∼c) c∼d
    -- We can write:
    example : ∀ {a b c d} → a ∼ b → b ∼ c → c ∼ d → a ∼ d
    example {a} {b} {c} {d} a∼b b∼c c∼d =
      begin
        a ∼⟨ a∼b ⟩
        b ∼⟨ b∼c ⟩
        c ∼⟨ c∼d ⟩
        d ∎

  -- Example: Using ≡-Reasoning
  module EqualityExample where
    open ≡-Reasoning

    example : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    example {a = a} {b} {c} a≡b b≡c =
      begin
        a ≡⟨ a≡b ⟩
        b ≡⟨ b≡c ⟩
        c ∎
```