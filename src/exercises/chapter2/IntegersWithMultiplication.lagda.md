---
layout: agda
title: "Integers with Multiplication"
section: "Exercises"
chapter: 2
number: 4
---

# Exercise 2.4: Integers with Multiplication

## Textbook Exercise

**Exercise 2.4.** Consider again the preorder (ℝ, ≤) from Example 2.3. Someone proposes 1 as a monoidal unit and ∗ (usual multiplication) as a monoidal product. But an expert walks by and says "that won't work." Figure out why, or prove the expert wrong!

**Note:** We work with integers (ℤ) instead of real numbers (ℝ) for this formalization.

## Agda Setup

```agda
module exercises.chapter2.IntegersWithMultiplication where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure)
open import Data.Integer using (ℤ; _*_; _≤_; +_; -[1+_])
open import Data.Integer.Properties using
  ( ≤-refl; ≤-trans
  ; *-identityˡ; *-identityʳ
  ; *-assoc; *-comm
  )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- The preorder structure from Example 2.3
ℤ-preorder : Preorder
ℤ-preorder = record
  { Carrier = ℤ
  ; _≤_ = _≤_
  ; isPreorder = record
      { reflexive = ≤-refl
      ; transitive = ≤-trans
      }
  }
```

## Problem

Determine whether (ℤ, ≤, 1, *) satisfies the conditions of Definition 2.1. Either construct the symmetric monoidal structure, or provide a counterexample showing it fails.

```agda
module _ where
  private
    -- A counterexample to monotonicity would consist of four integers
    -- and two proofs of ordering, plus a proof that the expected inequality fails
    MonotonicityCounterexample : Set
    MonotonicityCounterexample =
      ∃[ x₁ ] ∃[ x₂ ] ∃[ y₁ ] ∃[ y₂ ]
        (x₁ ≤ y₁) × (x₂ ≤ y₂) × ¬((x₁ * x₂) ≤ (y₁ * y₂))

  -- Either construct the monoidal structure, or give a counterexample
  exercise-2-4 : SymmetricMonoidalStructure ℤ-preorder ⊎ MonotonicityCounterexample
```

## Solution

**Strategy:** Multiplication is NOT monotonic on ℤ because of negative numbers. We construct a counterexample using x₁ = -1, x₂ = 5, y₁ = -1, y₂ = 6.

```agda
  open import Data.Integer.Base using (-≤-)
  open import Data.Nat as ℕ using (suc; zero)
  open import Data.Nat.Base using (s≤s; z≤n)
  open import Data.Nat.Properties using (<-irrefl; ≤-trans)
  open import Relation.Binary.PropositionalEquality using (refl)

  -- Counterexample: x₁ = -1, x₂ = 5, y₁ = -1, y₂ = 6
  -- We have: -1 ≤ -1 and 5 ≤ 6
  -- But: (-1) * 5 = -5 and (-1) * 6 = -6
  -- And: -5 ≰ -6 (since -5 > -6)

  exercise-2-4 = inj₂ counterexample
    where
      x₁ = -[1+ 0 ]  -- -1
      x₂ = + 5
      y₁ = -[1+ 0 ]  -- -1
      y₂ = + 6

      -- -1 ≤ -1 (reflexivity)
      x₁≤y₁ : x₁ ≤ y₁
      x₁≤y₁ = Data.Integer.Properties.≤-refl

      -- 5 ≤ 6
      x₂≤y₂ : x₂ ≤ y₂
      x₂≤y₂ = Data.Integer.Base.+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
        where
          open import Data.Integer.Base

      -- But (-1) * 5 = -5 and (-1) * 6 = -6, and -5 > -6
      -- x₁ * x₂ = -[1+ 0 ] * (+ 5) = -[1+ 4 ] = -5
      -- y₁ * y₂ = -[1+ 0 ] * (+ 6) = -[1+ 5 ] = -6
      -- We need to prove: ¬(-[1+ 4 ] ≤ -[1+ 5 ])
      product-not-monotone : ¬((x₁ * x₂) ≤ (y₁ * y₂))
      product-not-monotone (-≤- 5≤4) =
        -- -[1+ m ] ≤ -[1+ n ] is represented as -≤- with n ≤ m
        -- So -[1+ 4 ] ≤ -[1+ 5 ] gives us a proof that 5 ≤ 4
        -- From 5 ≤ 4 and 4 < 5, we derive 4 < 4 by transitivity, contradicting irreflexivity
        let 4<5 : 4 ℕ.< 5
            4<5 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
            4<4 : 4 ℕ.< 4
            4<4 = Data.Nat.Properties.≤-trans 4<5 5≤4
        in <-irrefl refl 4<4

      counterexample : MonotonicityCounterexample
      counterexample = x₁ , x₂ , y₁ , y₂ , x₁≤y₁ , x₂≤y₂ , product-not-monotone
```
