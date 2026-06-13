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

```text
Bool (≤ order):              Cost (≥ order):

  true                         ∞ ≥ ... ≥ 3 ≥ 0
   |
  false

⋁∅ = false (least in ≤)     ⋁∅ = ∞ (least in ≥... actually greatest!)
x ∨ y = OR(x,y)             x ∨ y = min(x,y) (least element ≥ both)
```

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
