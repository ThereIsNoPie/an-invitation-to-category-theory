---
layout: agda
title: "NMY-Category"
section: "Exercises"
chapter: 2
number: 41
---

# NMY-Category

## Textbook Exercise

**Exercise 2.41.** Recall the monoidal preorder NMY := (P, ≤, yes, min) from Exercise 2.18. Interpret what an NMY-category is.

**Exercise 2.18.** Consider the preorder (P, ≤) with Hasse diagram no → maybe → yes. We propose a monoidal structure with yes as the monoidal unit and "min" as the monoidal product.

## Agda Setup

```agda
module exercises.chapter2.NMYCategory where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder; SymmetricMonoidalStructure)
open import definitions.chapter2.VCategory using (VCategory)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## Problem

The ingredients are given by Exercise 2.18: the carrier {no, maybe, yes} with
the chain ordering, unit yes, and product min.

```text
no → maybe → yes
```

```agda
-- The carrier: {no, maybe, yes}
data Certainty : Set where
  no    : Certainty
  maybe : Certainty
  yes   : Certainty

-- The ordering: no ≤ maybe ≤ yes
data _≤C_ : Certainty → Certainty → Set where
  no≤no       : no ≤C no
  no≤maybe    : no ≤C maybe
  no≤yes      : no ≤C yes
  maybe≤maybe : maybe ≤C maybe
  maybe≤yes   : maybe ≤C yes
  yes≤yes     : yes ≤C yes

-- The monoidal product: min
min : Certainty → Certainty → Certainty
min no    _     = no
min maybe no    = no
min maybe maybe = maybe
min maybe yes   = maybe
min yes   c     = c
```

The task: build NMY as a symmetric monoidal preorder, say what an NMY-category
is, and interpret it.

```agda
-- NMY: the symmetric monoidal preorder (P, ≤, yes, min)
NMY : SymmetricMonoidalPreorder

-- An NMY-category is a category enriched in NMY
NMY-Category : Set₁
NMY-Category = VCategory NMY
```

## Solution: interpretation

An NMY-category X has objects and, for each pair x, y, a value X(x,y) in {no, maybe, yes}.

Axioms:

- Identity: yes ≤ X(x,x), so X(x,x) = yes
- Composition: min(X(x,y), X(y,z)) ≤ X(x,z)

Meaning: This is a "certainty of reachability" category:

- yes = "definitely can reach"
- maybe = "possibly can reach"
- no = "cannot reach"

The composition axiom says certainty is pessimistic: the weakest link in a chain determines overall certainty.

## Solution: construction

The preorder and monoidal structure laws are all finite case splits.

```agda
≤C-refl : ∀ {x} → x ≤C x
≤C-refl {no}    = no≤no
≤C-refl {maybe} = maybe≤maybe
≤C-refl {yes}   = yes≤yes

≤C-trans : ∀ {x y z} → x ≤C y → y ≤C z → x ≤C z
≤C-trans no≤no       q           = q
≤C-trans no≤maybe    maybe≤maybe = no≤maybe
≤C-trans no≤maybe    maybe≤yes   = no≤yes
≤C-trans no≤yes      yes≤yes     = no≤yes
≤C-trans maybe≤maybe q           = q
≤C-trans maybe≤yes   yes≤yes     = maybe≤yes
≤C-trans yes≤yes     yes≤yes     = yes≤yes

CertaintyPreorder : Preorder
CertaintyPreorder = record
  { Carrier = Certainty
  ; _≤_ = _≤C_
  ; isPreorder = record
    { reflexive = ≤C-refl
    ; transitive = ≤C-trans
    }
  }

min-mono : ∀ {x₁ x₂ y₁ y₂} → x₁ ≤C y₁ → x₂ ≤C y₂ → min x₁ x₂ ≤C min y₁ y₂
min-mono no≤no       _           = ≤C-refl
min-mono no≤maybe    no≤no       = no≤no
min-mono no≤maybe    no≤maybe    = no≤maybe
min-mono no≤maybe    no≤yes      = no≤maybe
min-mono no≤maybe    maybe≤maybe = no≤maybe
min-mono no≤maybe    maybe≤yes   = no≤maybe
min-mono no≤maybe    yes≤yes     = no≤maybe
min-mono no≤yes      no≤no       = no≤no
min-mono no≤yes      no≤maybe    = no≤maybe
min-mono no≤yes      no≤yes      = no≤yes
min-mono no≤yes      maybe≤maybe = no≤maybe
min-mono no≤yes      maybe≤yes   = no≤yes
min-mono no≤yes      yes≤yes     = no≤yes
min-mono maybe≤maybe no≤no       = no≤no
min-mono maybe≤maybe no≤maybe    = no≤maybe
min-mono maybe≤maybe no≤yes      = no≤maybe
min-mono maybe≤maybe maybe≤maybe = maybe≤maybe
min-mono maybe≤maybe maybe≤yes   = maybe≤maybe
min-mono maybe≤maybe yes≤yes     = maybe≤maybe
min-mono maybe≤yes   no≤no       = no≤no
min-mono maybe≤yes   no≤maybe    = no≤maybe
min-mono maybe≤yes   no≤yes      = no≤yes
min-mono maybe≤yes   maybe≤maybe = maybe≤maybe
min-mono maybe≤yes   maybe≤yes   = maybe≤yes
min-mono maybe≤yes   yes≤yes     = maybe≤yes
min-mono yes≤yes     q           = q

min-left-unit : ∀ {x} → min yes x ≡ x
min-left-unit {no}    = refl
min-left-unit {maybe} = refl
min-left-unit {yes}   = refl

min-right-unit : ∀ {x} → min x yes ≡ x
min-right-unit {no}    = refl
min-right-unit {maybe} = refl
min-right-unit {yes}   = refl

min-assoc : ∀ {x y z} → min (min x y) z ≡ min x (min y z)
min-assoc {no}    {_}     {_}     = refl
min-assoc {maybe} {no}    {_}     = refl
min-assoc {maybe} {maybe} {no}    = refl
min-assoc {maybe} {maybe} {maybe} = refl
min-assoc {maybe} {maybe} {yes}   = refl
min-assoc {maybe} {yes}   {no}    = refl
min-assoc {maybe} {yes}   {maybe} = refl
min-assoc {maybe} {yes}   {yes}   = refl
min-assoc {yes}   {no}    {_}     = refl
min-assoc {yes}   {maybe} {no}    = refl
min-assoc {yes}   {maybe} {maybe} = refl
min-assoc {yes}   {maybe} {yes}   = refl
min-assoc {yes}   {yes}   {z}     = refl

min-sym : ∀ {x y} → min x y ≡ min y x
min-sym {no}    {no}    = refl
min-sym {no}    {maybe} = refl
min-sym {no}    {yes}   = refl
min-sym {maybe} {no}    = refl
min-sym {maybe} {maybe} = refl
min-sym {maybe} {yes}   = refl
min-sym {yes}   {no}    = refl
min-sym {yes}   {maybe} = refl
min-sym {yes}   {yes}   = refl

NMYStructure : SymmetricMonoidalStructure CertaintyPreorder
NMYStructure = record
  { I = yes
  ; _⊗_ = min
  ; monotonicity = min-mono
  ; left-unit = λ {x} → min-left-unit {x}
  ; right-unit = λ {x} → min-right-unit {x}
  ; associativity = λ {x} {y} {z} → min-assoc {x} {y} {z}
  ; symmetry = λ {x} {y} → min-sym {x} {y}
  }

NMY = record
  { preorder = CertaintyPreorder
  ; structure = NMYStructure
  }
```

## Example

A two-object NMY-category: you can definitely stay where you are, you can
maybe get from A to B, and you can never get from B to A.

```agda
module ExampleNMYCategory where
  data TwoObj : Set where
    A B : TwoObj

  -- Hom-objects: A→A and B→B are "yes" (identity)
  -- A→B is "maybe", B→A is "no"
  hom : TwoObj → TwoObj → Certainty
  hom A A = yes
  hom A B = maybe
  hom B A = no
  hom B B = yes

  identity : ∀ {x} → yes ≤C hom x x
  identity {A} = yes≤yes
  identity {B} = yes≤yes

  composition : ∀ {x y z} → min (hom x y) (hom y z) ≤C hom x z
  composition {A} {A} {A} = yes≤yes
  composition {A} {A} {B} = maybe≤maybe
  composition {A} {B} {A} = no≤yes
  composition {A} {B} {B} = maybe≤maybe
  composition {B} {A} {A} = no≤no
  composition {B} {A} {B} = no≤yes
  composition {B} {B} {A} = no≤no
  composition {B} {B} {B} = yes≤yes

  TwoCertainty : NMY-Category
  TwoCertainty = record
    { Ob = TwoObj
    ; hom = hom
    ; identity = identity
    ; composition = composition
    }
```
