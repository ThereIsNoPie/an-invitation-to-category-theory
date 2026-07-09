---
layout: agda
title: "Joins in Bool and Cost"
section: "Exercises"
chapter: 2
number: 68
---

# Joins in Bool and Cost

## Textbook Exercise

**Exercise 2.68.**

1. What is $\bigvee \varnothing$, which we generally denote $\mathbf{0}$, in the case
   - (a) $\mathcal{V} = \mathbf{Bool} = (\mathbb{B}, \leq, \mathsf{true}, \wedge)$?
   - (b) $\mathcal{V} = \mathbf{Cost} = ([0,\infty], \geq, 0, +)$?

2. What is the join $x \vee y$ in the case
   - (a) $\mathcal{V} = \mathbf{Bool}$, and $x, y \in \mathbb{B}$ are booleans?
   - (b) $\mathcal{V} = \mathbf{Cost}$, and $x, y \in [0,\infty]$ are distances?

## Agda Setup

```agda
module exercises.chapter2.JoinsInBoolAndCost where

open import definitions.chapter1.MeetJoin using (IsJoin)
open import examples.chapter2.BoolAnd using (_≤𝔹_; ≤-refl; f≤t)
open import examples.chapter2.Cost using ([0,∞]; ∞; _≥_)
open import plumbing.Reals using (∞-greatest; min; min-lb-l; min-lb-r; min-glb)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## Problem

The bottom element $\mathbf{0} = \bigvee \varnothing$ is the least element in the preorder (anything is an upper bound of $\varnothing$, so the *least* upper bound is the smallest element). The binary join $x \vee y$ is the least upper bound of $\lbrace x, y \rbrace$.

Arrows point *up the order* (from smaller to larger in the preorder). The trap:
Cost uses the reversed order ≥, so the numerically greatest distance ∞ sits at
the *bottom*.

```svg
<svg viewBox="0 0 480 270" role="img" aria-label="Hasse diagrams: Bool under ≤ with false below true; Cost under ≥ with ∞ at the bottom, then 3, 1, 0 at the top">
  <text x="120" y="30" font-size="16" font-weight="bold" text-anchor="middle" fill="currentColor">Bool (≤)</text>
  <text x="120" y="70" font-size="16" text-anchor="middle" fill="currentColor">true</text>
  <text x="120" y="200" font-size="16" text-anchor="middle" fill="currentColor">false</text>
  <line x1="120" y1="184" x2="120" y2="78" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <text x="120" y="235" font-size="14" text-anchor="middle" fill="var(--agda-function)">⋁∅ = false (least)</text>

  <text x="340" y="30" font-size="16" font-weight="bold" text-anchor="middle" fill="currentColor">Cost (≥)</text>
  <text x="340" y="65" font-size="16" text-anchor="middle" fill="currentColor">0</text>
  <text x="340" y="110" font-size="16" text-anchor="middle" fill="currentColor">1</text>
  <text x="340" y="155" font-size="16" text-anchor="middle" fill="currentColor">3</text>
  <text x="340" y="200" font-size="16" text-anchor="middle" fill="currentColor">∞</text>
  <line x1="340" y1="184" x2="340" y2="161" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="340" y1="139" x2="340" y2="116" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="340" y1="94" x2="340" y2="71" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <text x="340" y="235" font-size="14" text-anchor="middle" fill="var(--agda-function)">⋁∅ = ∞ (least in ≥)</text>
  <text x="340" y="255" font-size="12" text-anchor="middle" fill="currentColor" opacity="0.7">numerically greatest!</text>
</svg>
```

So the joins are: in Bool, $x \vee y = \mathsf{OR}(x, y)$; in Cost,
$x \vee y = \min(x, y)$ — the least element that is ≥ both.

```agda
-- 1a. Bottom of Bool: ⋁∅ = false
bool-bottom : IsJoin _≤𝔹_ false (λ _ → ⊥)

-- 1b. Bottom of Cost: ⋁∅ = ∞
cost-bottom : IsJoin _≥_ ∞ (λ _ → ⊥)

-- 2a. Binary join in Bool: x ∨ y = logical OR
bool-join : ∀ x y → IsJoin _≤𝔹_ (x ∨ y) (λ b → (b ≡ x) ⊎ (b ≡ y))

-- 2b. Binary join in Cost: x ∨ y = min(x, y)
cost-join : ∀ x y → IsJoin _≥_ (min x y) (λ c → (c ≡ x) ⊎ (c ≡ y))
```

## Solution

```agda
-- 1a. false is the bottom of Bool: vacuously an upper bound of ∅,
--     and false ≤ everything
bool-bottom = ((λ ()) , λ {_} _ → go _)
  where
    go : ∀ x → false ≤𝔹 x
    go false = ≤-refl
    go true = f≤t

-- 1b. ∞ is the bottom of Cost: vacuously ≥ everything in ∅,
--     and ∞ ≥ everything
cost-bottom = ((λ ()) , λ {_} _ → ∞-greatest)

-- 2a. Logical OR is the binary join in Bool (case split on all four combinations)
bool-join false false = ((λ { (inj₁ refl) → ≤-refl ; (inj₂ refl) → ≤-refl })
                        , λ h → h (inj₁ refl))
bool-join false true  = ((λ { (inj₁ refl) → f≤t ; (inj₂ refl) → ≤-refl })
                        , λ h → h (inj₂ refl))
bool-join true  false = ((λ { (inj₁ refl) → ≤-refl ; (inj₂ refl) → f≤t })
                        , λ h → h (inj₁ refl))
bool-join true  true  = ((λ { (inj₁ refl) → ≤-refl ; (inj₂ refl) → ≤-refl })
                        , λ h → h (inj₁ refl))

-- 2b. min is the binary join in Cost (with ≥ order)
cost-join x y = ( (λ { (inj₁ refl) → min-lb-l ; (inj₂ refl) → min-lb-r })
                , λ h → min-glb (h (inj₁ refl)) (h (inj₂ refl)))
```
