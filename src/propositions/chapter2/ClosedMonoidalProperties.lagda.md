---
layout: agda
title: "Properties of Closed Monoidal Preorders"
section: "Propositions"
chapter: 2
number: 64
---

# Properties of Closed Monoidal Preorders

## Textbook Statement

**Proposition 2.64.** Suppose $\mathcal{V} = (V, \leq, I, \otimes, \multimap)$ is a symmetric monoidal preorder that is closed. Then:

(a) For every $v \in V$, the monotone map $(-\otimes v) : (V, \leq) \to (V, \leq)$ is left adjoint to $(v \multimap -) : (V, \leq) \to (V, \leq)$.

(b) For any element $v \in V$ and set of elements $A \subseteq V$, if the join $\bigvee_{a \in A} a$ exists then so does $\bigvee_{a \in A} v \otimes a$ and we have $v \otimes \bigvee_{a \in A} a \cong \bigvee_{a \in A} (v \otimes a)$.

(c) For any $v, w \in V$, we have $v \otimes (v \multimap w) \leq w$.

(d) For any $v \in V$, we have $v \cong (I \multimap v)$.

(e) For any $u, v, w \in V$, we have $(u \multimap v) \otimes (v \multimap w) \leq (u \multimap w)$.

## Agda Setup

```agda
module propositions.chapter2.ClosedMonoidalProperties where

open import definitions.chapter2.MonoidalClosed
  using (MonoidalClosedPreorder; IsMonoidalClosed)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import plumbing.EquationalReasoning using (module Goal-Reasoning)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
```

## Properties

Each signature maps onto one item of the proposition, reading $v \multimap w$
as a single-use converter from $v$ to $w$. Item (a) is the adjunction that
*defines* closure; (c), (d), (e) are its consequences. Item (b) — that
$-\otimes v$ preserves joins — also follows from (a), since left adjoints
preserve joins (Proposition 1.104), but it needs the joins machinery, so we
record it in prose only.

```agda
module Properties (MCP : MonoidalClosedPreorder) where
  open MonoidalClosedPreorder MCP
  open Goal-Reasoning
  open ≤-Reasoning

  -- (a) (−⊗v) ⊣ (v⊸−): the adjunction is exactly curry/uncurry
  adjunctionᴸ : ∀ {a v w} → (a ⊗ v) ≤ w → a ≤ (v ⊸ w)
  adjunctionᴿ : ∀ {a v w} → a ≤ (v ⊸ w) → (a ⊗ v) ≤ w

  -- (c) evaluation: a v and a single-use v-to-w converter yield a w
  eval : ∀ {v w} → (v ⊗ (v ⊸ w)) ≤ w

  -- (d) having a v = having a single-use nothing-to-v converter
  unit-iso-1 : ∀ {v} → v ≤ (I ⊸ v)
  unit-iso-2 : ∀ {v} → (I ⊸ v) ≤ v

  -- (e) converters compose: a u-to-v and a v-to-w give a u-to-w
  hom-compose : ∀ {u v w} → ((u ⊸ v) ⊗ (v ⊸ w)) ≤ (u ⊸ w)
```

## Proof

```agda
  -- (a) is definitional: closure gives exactly this Galois connection
  adjunctionᴸ = curry
  adjunctionᴿ = uncurry

  -- (c) uncurry reflexivity (v⊸w)≤(v⊸w) to (v⊸w)⊗v ≤ w, then commute.
  -- Made explicit: every step reshapes the whole judgement, so it is a pure
  -- goal-directed chain — read top-down from the goal.
  eval {v} {w} =
      (v ⊗ (v ⊸ w)) ≤ w    by subst (_≤ w) symmetry ⟵
      ((v ⊸ w) ⊗ v) ≤ w     by uncurry ⟵
      (v ⊸ w) ≤ (v ⊸ w)     witness reflexive

  -- (d) forward: v⊗I = v ≤ v, so curry gives v ≤ (I⊸v)
  unit-iso-1 {v} = curry (subst (_≤ v) (sym right-unit) reflexive)
  -- (d) back: (I⊸v) = I⊗(I⊸v) ≤ v by eval
  unit-iso-2 {v} = subst (_≤ v) left-unit eval

  -- (e) Made explicit. The outer skeleton is goal-directed: every step reshapes
  -- the whole judgement, so read it top-down from the goal. `curry` transposes
  -- across the adjunction, then two `subst`s reassociate and commute the u factor
  -- to the front. The base case is a plain ≤-chain: feed u into the u-to-v
  -- converter to obtain v, then feed that v into the v-to-w converter to obtain w.
  hom-compose {u} {v} {w} =
      ((u ⊸ v) ⊗ (v ⊸ w)) ≤ (u ⊸ w)         by curry ⟵
      (((u ⊸ v) ⊗ (v ⊸ w)) ⊗ u) ≤ w         by subst (_≤ w) symmetry ⟵
      (u ⊗ ((u ⊸ v) ⊗ (v ⊸ w))) ≤ w         by subst (_≤ w) associativity ⟵
      ((u ⊗ (u ⊸ v)) ⊗ (v ⊸ w)) ≤ w         witness
        (begin
          (u ⊗ (u ⊸ v)) ⊗ (v ⊸ w)  ≤⟨ monotonicity eval reflexive ⟩
          v ⊗ (v ⊸ w)               ≤⟨ eval ⟩
          w                         ∎)
```

## Interpretation

These properties explain the intuition behind monoidal closed preorders:

- **(c)** "If I have a $v$ and a single-use $v$-to-$w$ converter, I can get a $w$."

- **(d)** "Having a $v$ is the same as having a single-use nothing-to-$v$ converter."

- **(e)** "If I have a single-use $u$-to-$v$ converter and a single-use $v$-to-$w$ converter, I can get a single-use $u$-to-$w$ converter."

These are exactly the properties we expect if we think of $(v \multimap w)$ as encoding "the way to get from $v$ to $w$".
