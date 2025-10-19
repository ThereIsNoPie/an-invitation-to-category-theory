---
layout: agda
title: "Classical Postulates"
section: "Plumbing"
---

# Classical Postulates

To formalize mathematics as presented in classical textbooks like "An Invitation to Category Theory," we need to postulate several principles that are assumed in set theory but not provable in constructive type theory.

## Function Extensionality

In classical mathematics, two functions are considered equal if they produce the same outputs for all inputs. In type theory, this requires an axiom.

```agda
module plumbing.ClassicalPostulates where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; Σ-syntax)

postulate
  funext : {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
```

**Why needed**: The textbook freely identifies functions that agree pointwise, e.g., when showing two partitions are "the same."

## Propositional Extensionality

Two propositions are equal if they are logically equivalent.

```agda
postulate
  propext : {P Q : Set} → (P → Q) → (Q → P) → P ≡ Q
```

**Why needed**: Classical logic treats "P iff Q" as meaning "P = Q as propositions."

## Proof Irrelevance

All proofs of the same proposition are equal. How you prove something doesn't matter, only that it's true.

```agda
postulate
  proof-irrelevance : {P : Set} (p q : P) → p ≡ q
```

**Why needed**: The textbook doesn't distinguish between different proofs of the same fact. For example, when showing two parts satisfy the same properties, we don't care *how* they satisfy them.

## Quotient Types

Given an equivalence relation ∼ on a set A, we can form the quotient A/∼ whose elements are the equivalence classes.

```agda
postulate
  _/_ : (A : Set) → (A → A → Set) → Set
  [_] : {A : Set} {_∼_ : A → A → Set} → A → A / _∼_

  -- Soundness: related elements have equal quotient images
  quotient-sound : {A : Set} {_∼_ : A → A → Set} {a b : A} →
                   a ∼ b → _≡_ {A = A / _∼_} [ a ] [ b ]

  -- Effectiveness: equal quotient elements come from related elements
  quotient-effective : {A : Set} {_∼_ : A → A → Set} {a b : A} →
                       _≡_ {A = A / _∼_} [ a ] [ b ] → a ∼ b

  -- Surjectivity: every quotient element has a representative
  quotient-surjective : {A : Set} {_∼_ : A → A → Set} (q : A / _∼_) →
                        Σ[ a ∈ A ] ([ a ] ≡ q)
```

**Why needed**: The textbook freely uses "the set of equivalence classes" as in Definition 1.16 (Quotient) and throughout. Without quotient types, we cannot properly represent this at the right universe level in Agda.

## Notes

These postulates are:
- **Consistent** with constructive type theory (they don't introduce contradictions)
- **Standard** in classical mathematics (automatically satisfied in set theory)
- **Available** in Cubical Agda (where they are provable, not postulated)
- **Necessary** to faithfully formalize classical textbook mathematics in standard Agda

For propositions like the partition-equivalence correspondence (Proposition 1.14), quotient types are essential.
```