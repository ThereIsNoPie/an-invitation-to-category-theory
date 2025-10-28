---
layout: agda
title: "Modal Operators as Closure Operators"
section: "Examples"
chapter: 1
number: 115
---

# Modal Operators as Closure Operators

## Textbook Description

**Example 1.115 (Modal operators).** Another example of closure operators comes from logic. This will be discussed in the final chapter of the book, in particular Section 7.4.5, but we will give a quick overview here. In essence, logic is the study of when one formal statement – or proposition – implies another. For example, if n is prime then n is not a multiple of 6, or if it is raining then the ground is getting wetter. Here "n is prime," "n is not a multiple of 6," "it is raining," and "the ground is getting wetter" are propositions, and we gave two implications.

Take the set of all propositions and order them by p ≤ q iff p implies q, denoted p ⇒ q. Since p ⇒ p and since whenever p ⇒ q and q ⇒ r, we also have p ⇒ r, this is indeed a preorder.

A closure operator on it is often called a modal operator. It is a function j from propositions to propositions, for which p ⇒ j(p) and j(j(p)) = j(p). An example of a j is "assuming Bob is in San Diego . . . ." Think of this as a proposition B; so "assuming Bob is in San Diego, p" means B ⇒ p. Let's see why B ⇒ − is a closure operator.

If p is true then "assuming Bob is in San Diego, p" is still true. Suppose that "assuming Bob is in San Diego it is the case that, 'assuming Bob is in San Diego, p' is true." It follows that "assuming Bob is in San Diego, p" is true. So we have seen, at least informally, that "assuming Bob is in San Diego . . . " is a closure operator.

## Agda Setup

```agda
module examples.chapter1.ModalOperators where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_; suc)

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
```

## The Example

We formalize modal operators using the **Curry-Howard correspondence**: propositions are types, and implication is the function type.

### Key Type Definitions

```agda
-- Propositions are types (Curry-Howard correspondence)
Prop : Set₁
Prop = Set

-- Logical implication is the function type
_⇒_ : Prop → Prop → Prop
p ⇒ q = p → q

-- The implication relation forms a preorder
⇒-reflexive : ∀ {p : Prop} → p ⇒ p
⇒-reflexive x = x

⇒-transitive : ∀ {p q r : Prop} → p ⇒ q → q ⇒ r → p ⇒ r
⇒-transitive f g x = g (f x)
```

## Attempting to Use Standard Definitions

Let's try to form a preorder using our standard `Preorder` definition:

```agda
-- Attempting to use the standard Preorder:
--
-- ⇒-isPreorder : IsPreorder _⇒_
-- ⇒-isPreorder = record
--   { reflexive = ⇒-reflexive
--   ; transitive = ⇒-transitive
--   }
--
-- PropPreorder : Preorder
-- PropPreorder = record
--   { Carrier = Prop        -- ERROR! Set₁ != Set
--   ; _≤_ = _⇒_
--   ; isPreorder = ⇒-isPreorder
--   }
```

**The problem**: Our `definitions.Preorder` expects `Carrier : Set`, but `Prop = Set` has type `Set₁`. This is a **universe level mismatch**.

## Universe Levels: A Brief Explanation

We have been avoiding universe levels because they make type signatures confusing. However, we need them here.

Please read about them [in the official docs](https://agda.readthedocs.io/en/latest/language/universe-levels.html).

### Implementation

The Agda standard library provides universe-polymorphic versions. We'll define our own simplified versions here:

```agda
-- Universe-polymorphic preorder
record IsPreorder₁ {c ℓ : Level} {A : Set c} (_≤_ : A → A → Set ℓ) : Set (c ⊔ ℓ) where
  field
    reflexive  : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

record Preorder₁ (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where
  field
    Carrier    : Set c
    _≤_        : Carrier → Carrier → Set ℓ
    isPreorder : IsPreorder₁ _≤_

  open IsPreorder₁ isPreorder public

-- Universe-polymorphic monotonic functions
Monotonic₁ : {c ℓ : Level} {A B : Set c} → (A → A → Set ℓ) → (B → B → Set ℓ) → (A → B) → Set (c ⊔ ℓ)
Monotonic₁ {A = A} {B = B} _≤A_ _≤B_ f = ∀ {x y : A} → x ≤A y → f x ≤B f y

-- Universe-polymorphic closure operator
record ClosureOperator₁ {c ℓ : Level} (P : Preorder₁ c ℓ) : Set (c ⊔ ℓ) where
  open Preorder₁ P

  field
    j : Carrier → Carrier
    j-monotonic : Monotonic₁ _≤_ _≤_ j
    extensive : ∀ (x : Carrier) → x ≤ j x
    idempotent : ∀ (x : Carrier) → (j (j x) ≤ j x) × (j x ≤ j (j x))
```

These definitions use **level parameters** (`c` for carrier level, `ℓ` for relation level) so they work at any universe level.

## The Preorder of Propositions

Now we can form the preorder!

```agda
-- Implication forms a preorder
⇒-isPreorder₁ : IsPreorder₁ _⇒_
⇒-isPreorder₁ = record
  { reflexive = ⇒-reflexive
  ; transitive = ⇒-transitive
  }

-- This type signature uses "levels" which we have been avoiding
-- Carrier level: 1 (since Prop = Set : Set₁)
-- Relation level: 0 (since p ⇒ q = p → q : Set)
PropPreorder : Preorder₁ (suc Level.zero) Level.zero
PropPreorder = record
  { Carrier = Prop
  ; _≤_ = _⇒_
  ; isPreorder = ⇒-isPreorder₁
  }
```

## The Modal Operator

Given any proposition B, "assuming B, ..." is a closure operator.

```agda
module ModalOperatorConstruction (B : Prop) where
  open Preorder₁ PropPreorder

  -- The modal operator: "assuming B, p" means B → p
  assuming-B : Prop → Prop
  assuming-B p = B ⇒ p
```

### The Closure Operator Properties

```agda
  -- Extensivity: If p is true, then "assuming B, p" is true
  -- Proof: p → (B → p) is the constant function
  assuming-B-extensive : ∀ (p : Prop) → p ⇒ assuming-B p

  -- Idempotence: (B → (B → p)) ⇔ (B → p)
  assuming-B-idempotent : ∀ (p : Prop) → (assuming-B (assuming-B p) ⇒ assuming-B p)
                                        × (assuming-B p ⇒ assuming-B (assuming-B p))

  -- Monotonicity: If p ⇒ q, then (B → p) ⇒ (B → q)
  assuming-B-monotonic : Monotonic₁ _≤_ _≤_ assuming-B

  -- The modal operator as a closure operator
  assuming-B-closure : ClosureOperator₁ PropPreorder
```

### Implementation

**Strategy**: Use the Curry-Howard correspondence directly - these are just functions!

```agda
  -- Extensivity: constant function
  assuming-B-extensive p = λ x b → x

  -- Idempotence forward: apply to same argument twice
  assuming-B-idempotent-fwd : ∀ (p : Prop) → assuming-B (assuming-B p) ⇒ assuming-B p
  assuming-B-idempotent-fwd p = λ f b → f b b

  -- Idempotence backward: ignore first argument
  assuming-B-idempotent-bwd : ∀ (p : Prop) → assuming-B p ⇒ assuming-B (assuming-B p)
  assuming-B-idempotent-bwd p = λ f b₁ b₂ → f b₂

  assuming-B-idempotent p = assuming-B-idempotent-fwd p , assuming-B-idempotent-bwd p

  -- Monotonicity: function composition
  assuming-B-monotonic {p} {q} p⇒q = λ b⇒p b → p⇒q (b⇒p b)

  -- The modal operator as a closure operator
  assuming-B-closure = record
    { j = assuming-B
    ; j-monotonic = assuming-B-monotonic
    ; extensive = assuming-B-extensive
    ; idempotent = assuming-B-idempotent
    }
```

## Interpretation: Why These Properties Hold

Let's understand the computational content of each property:

**1. Extensivity**: `λ x b → x`
- Given a proof `x : p`, we need a function `B → p`
- The constant function `λ b → x` ignores B and returns the proof of p
- Captures: "if p is true, then 'assuming anything, p' is true"

**2. Idempotence forward**: `λ f b → f b b`
- Given `f : B → (B → p)`, we need `B → p`
- Apply f to get `B → p`, then apply that to the same B
- Captures: "assuming B that (assuming B, p)" simplifies to "assuming B, p"

**3. Idempotence backward**: `λ f b₁ b₂ → f b₂`
- Given `f : B → p`, we need `B → (B → p)`
- Take two B's and use the second one with f
- Captures: "assuming B, p" embeds into "assuming B that (assuming B, p)"

**4. Monotonicity**: `λ p⇒q b⇒p b → p⇒q (b⇒p b)`
- Given `p⇒q : p → q` and `b⇒p : B → p`, we need `B → q`
- Function composition: `B ⟶ p ⟶ q`
- Captures: implications are preserved under assumptions

## Concrete Examples

Let's see this with specific propositions:

```agda
module ConcreteModalExample where
  -- Some example propositions (types)
  postulate
    BobInSanDiego : Prop
    GroundIsWet : Prop
    ItIsRaining : Prop

  open ModalOperatorConstruction BobInSanDiego

  -- "Assuming Bob is in San Diego, the ground is wet"
  -- is the function type: BobInSanDiego → GroundIsWet
  assuming-bob-ground-wet : Prop
  assuming-bob-ground-wet = assuming-B GroundIsWet

  -- If we know "it raining implies ground is wet"
  postulate
    raining-implies-wet : ItIsRaining ⇒ GroundIsWet

  -- Then by monotonicity:
  -- "assuming Bob is in SD, it's raining" ⇒ "assuming Bob is in SD, ground is wet"
  derived-implication : (BobInSanDiego ⇒ ItIsRaining) ⇒ (BobInSanDiego ⇒ GroundIsWet)
  derived-implication = assuming-B-monotonic raining-implies-wet
```

## Connection to Modal Logic

This example bridges to **modal logic**, where operators like:
- □p ("necessarily p")
- ◇p ("possibly p")
- "Assuming condition C, p"

are studied systematically. The closure operator perspective gives us:
- **Extensivity**: Truth is preserved
- **Idempotence**: Repeated application doesn't change meaning
- **Monotonicity**: Implications are preserved

## Summary

This formalization demonstrates:
1. **Modal operators are closure operators** - using direct computational content
2. **Universe polymorphism is necessary** - to work with `Prop = Set` at `Set₁` level
3. **No postulates needed** - all properties proven using lambda terms
4. **Curry-Howard gives intuition** - modal logic has computational meaning

The key insight: "assuming B, ..." is not abstract nonsense - it's literally a function type `B → ...`, and the closure operator properties are simple, beautiful lambda terms.
```
