---
layout: agda
title: "Properties of Closed Monoidal Preorders"
section: "Propositions"
chapter: 2
number: 64
---

# Properties of Closed Monoidal Preorders

## Textbook Statement

**Proposition 2.61.** Suppose $\mathcal{V} = (V, \leq, I, \otimes, \multimap)$ is a symmetric monoidal preorder that is closed. Then:

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
```

## Properties

```agda
module Properties (MCP : MonoidalClosedPreorder) where
  open MonoidalClosedPreorder MCP

  -- (a) The adjunction is exactly the definition of monoidal closed
  -- (-⊗v) ⊣ (v⊸-)
  -- This is just the curry/uncurry isomorphism

  -- (c) Evaluation: v ⊗ (v ⊸ w) ≤ w
  -- Proof: From reflexivity (v ⊸ w) ≤ (v ⊸ w), uncurry gives
  --        ((v ⊸ w) ⊗ v) ≤ w, then use symmetry
  eval : ∀ {v w} → (v ⊗ (v ⊸ w)) ≤ w
  eval {v} {w} = subst (_≤ w) symmetry (uncurry reflexive)

  -- (d) v ≅ (I ⊸ v)
  -- One direction: v ≤ (I ⊸ v)
  -- Proof: From v ⊗ I = v ≤ v, curry gives v ≤ (I ⊸ v)
  unit-iso-1 : ∀ {v} → v ≤ (I ⊸ v)
  unit-iso-1 {v} = curry (subst (_≤ v) (sym right-unit) reflexive)

  -- Other direction: (I ⊸ v) ≤ v
  -- Proof: (I ⊸ v) = I ⊗ (I ⊸ v) ≤ v by eval
  unit-iso-2 : ∀ {v} → (I ⊸ v) ≤ v
  unit-iso-2 {v} = subst (_≤ v) left-unit eval

  -- (e) Composition of homs: (u ⊸ v) ⊗ (v ⊸ w) ≤ (u ⊸ w)
  -- Proof: By curry, we need ((u ⊸ v) ⊗ (v ⊸ w)) ⊗ u ≤ w
  --        Using associativity and symmetry to rearrange
  hom-compose : ∀ {u v w} → ((u ⊸ v) ⊗ (v ⊸ w)) ≤ (u ⊸ w)
  hom-compose {u} {v} {w} = curry goal
    where
      -- u ⊗ (u ⊸ v) ≤ v
      step1 : (u ⊗ (u ⊸ v)) ≤ v
      step1 = eval

      -- (u ⊗ (u ⊸ v)) ⊗ (v ⊸ w) ≤ v ⊗ (v ⊸ w)
      step2 : ((u ⊗ (u ⊸ v)) ⊗ (v ⊸ w)) ≤ (v ⊗ (v ⊸ w))
      step2 = monotonicity step1 reflexive

      -- v ⊗ (v ⊸ w) ≤ w
      step3 : (v ⊗ (v ⊸ w)) ≤ w
      step3 = eval

      -- (u ⊗ (u ⊸ v)) ⊗ (v ⊸ w) ≤ w
      combined : ((u ⊗ (u ⊸ v)) ⊗ (v ⊸ w)) ≤ w
      combined = transitive step2 step3

      -- Goal: ((u ⊸ v) ⊗ (v ⊸ w)) ⊗ u ≤ w
      -- First get: u ⊗ ((u ⊸ v) ⊗ (v ⊸ w)) ≤ w
      -- by associativity: (u ⊗ (u ⊸ v)) ⊗ (v ⊸ w) = u ⊗ ((u ⊸ v) ⊗ (v ⊸ w))
      step4 : (u ⊗ ((u ⊸ v) ⊗ (v ⊸ w))) ≤ w
      step4 = subst (_≤ w) associativity combined

      -- Then use symmetry: ((u ⊸ v) ⊗ (v ⊸ w)) ⊗ u = u ⊗ ((u ⊸ v) ⊗ (v ⊸ w))
      goal : (((u ⊸ v) ⊗ (v ⊸ w)) ⊗ u) ≤ w
      goal = subst (_≤ w) symmetry step4
```

## Interpretation

These properties explain the intuition behind monoidal closed preorders:

- **(c)** "If I have a $v$ and a single-use $v$-to-$w$ converter, I can get a $w$."

- **(d)** "Having a $v$ is the same as having a single-use nothing-to-$v$ converter."

- **(e)** "If I have a single-use $u$-to-$v$ converter and a single-use $v$-to-$w$ converter, I can get a single-use $u$-to-$w$ converter."

These are exactly the properties we expect if we think of $(v \multimap w)$ as encoding "the way to get from $v$ to $w$".
