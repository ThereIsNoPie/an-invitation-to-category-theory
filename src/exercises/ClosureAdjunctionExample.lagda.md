---
layout: agda
title: "Closure Adjunction Example"
section: "Exercises"
chapter: 1
number: 117
---

# Closure Adjunction Example

## Textbook Exercise

**Exercise 1.117.** 
```text
Let S = {1, 2, 3}. Let's try to understand the adjunction discussed above.

1. Come up with any preorder relation ≤ on S, and define U(≤) to be the subset U(≤) := {(s₁, s₂) | s₁ ≤ s₂} ⊆ S × S, i.e. U(≤) is the image of ≤ under the inclusion Pos(S) → Rel(S), the relation "underlying" the preorder.

2. Come up with any two binary relations Q ⊆ S × S and Q' ⊆ S × S such that Q ⊆ U(≤) but Q' ⊈ U(≤). Note that your choice of Q, Q' do not have to come from preorders.

We now want to check that, in this case, the closure operation Cl is really left adjoint to the "underlying relation" map U.

3. Concretely (without using the assertion that there is some sort of adjunction), show that Cl(Q) ⊑ ≤, where ⊑ is the order on Pos(S), defined immediately above this exercise.

4. Concretely show that Cl(Q') ⊈ ≤.
```

## Context

For any set S, there is a set Pos(S) consisting of all preorder relations on S. There is a preorder structure ⊑ on Pos(S) given by inclusion: ≤₁ ⊑ ≤₂ if (a ≤₁ b → a ≤₂ b) for every a, b ∈ S.

Every preorder relation is a relation, so we have an inclusion U : Pos(S) → Rel(S). This is the right adjoint of a Galois connection. Its left adjoint is Cl : Rel(S) → Pos(S), which takes the reflexive and transitive closure of a relation.

## Agda Setup

```agda
module exercises.ClosureAdjunctionExample where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Level using (Level; _⊔_) renaming (suc to ℓsuc)
open import Relation.Binary using (IsPreorder; Preorder; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Our set S = {1, 2, 3}
S : Set
S = Fin 3

-- Pattern synonyms for readability
pattern s₁ = zero
pattern s₂ = suc zero
pattern s₃ = suc (suc zero)

-- Universe-polymorphic binary relation
BinRel : ∀ {ℓ} → Set ℓ → (ℓ' : Level) → Set (ℓ ⊔ ℓsuc ℓ')
BinRel {ℓ} A ℓ' = Rel A ℓ'

-- Simple IsPreorder record for our purposes
record SimpleIsPreorder {ℓ ℓ'} {A : Set ℓ} (_≤_ : BinRel A ℓ') : Set (ℓ ⊔ ℓ') where
  field
    reflexive  : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

-- Pos(S): The set of all preorders on S
-- For our S : Set, relations at level 0, so Pos S : Set₁
Pos : Set → Set₁
Pos A = Σ (BinRel A Level.zero) (SimpleIsPreorder {Level.zero} {Level.zero})

-- The preorder structure on Pos(S) given by inclusion: ≤₁ ⊑ ≤₂ iff ∀ a b → a ≤₁ b → a ≤₂ b
_⊑_ : Pos S → Pos S → Set
(R₁ , _) ⊑ (R₂ , _) = ∀ {a b} → R₁ a b → R₂ a b

-- ⊑ forms a preorder on Pos(S)
⊑-reflexive : ∀ {P : Pos S} → P ⊑ P
⊑-reflexive {(R , _)} x = x

⊑-transitive : ∀ {P₁ P₂ P₃ : Pos S} → P₁ ⊑ P₂ → P₂ ⊑ P₃ → P₁ ⊑ P₃
⊑-transitive {(R₁ , _)} {(R₂ , _)} {(R₃ , _)} f g x = g (f x)

-- Standard library preorder structure for Pos(S)
-- Universe levels:
-- - Pos S : Set₁ 
-- - _≡_ on Pos S : Pos S → Pos S → Set₁ 
-- - _⊑_ : Pos S → Pos S → Set

open import Relation.Binary.PropositionalEquality as PE

⊑-isPreorder : IsPreorder _≡_ _⊑_
⊑-isPreorder = record
  { isEquivalence = record 
    { refl = refl
    ; sym = PE.sym
    ; trans = PE.trans
    }
  ; reflexive = λ {x} {y} x≡y → PE.subst (λ z → x ⊑ z) x≡y (⊑-reflexive {x})
  ; trans = λ {x} {y} {z} → ⊑-transitive {x} {y} {z}
  }

-- The preorder of preorders on S using standard library
-- Successfully constructed with proper universe level handling:
-- - Carrier level: 1 (since Pos S : Set₁)
-- - Equality level: 1 (since _≡_ on Set₁ types has type Set₁)  
-- - Relation level: 0 (since _⊑_ : Pos S → Pos S → Set)
PosPreorder : Preorder _ _ _
PosPreorder = record
  { Carrier = Pos S
  ; _≈_ = _≡_
  ; _≲_ = _⊑_
  ; isPreorder = ⊑-isPreorder
  }

-- U: The "underlying relation" function from Pos(S) to Rel(S)
-- This extracts the relation from a preorder, forgetting the preorder structure
U : Pos S → BinRel S Level.zero
U (R , _) = R

-- Alternative notation that matches the mathematical presentation
-- U(≤) extracts the underlying relation from a preorder ≤
U-notation : ∀ (≤ : BinRel S Level.zero) → SimpleIsPreorder ≤ → BinRel S Level.zero
U-notation ≤ _ = ≤
```

## Problem

We'll work with S = {1, 2, 3} and demonstrate the Galois connection Cl ⊣ U.

```agda
-- Reflexive-transitive closure of a relation
data Cl (R : BinRel S Level.zero) : BinRel S Level.zero where
  incl      : ∀ {a b} → R a b → Cl R a b           -- Include original relation
  cl-refl   : ∀ {a} → Cl R a a                     -- Reflexivity
  cl-trans  : ∀ {a b c} → Cl R a b → Cl R b c → Cl R a c  -- Transitivity

-- Cl as a function from BinRel S to Pos S
Cl-to-PosS : BinRel S Level.zero → Pos S
Cl-to-PosS R = (Cl R , record { reflexive = cl-refl ; transitive = cl-trans })

module Exercise where
  -- Part 1: Define a preorder relation on S
  _≤_ : BinRel S Level.zero
  ≤-isPreorder : SimpleIsPreorder _≤_
  
  -- The preorder ≤ as an element of PosS
  ≤-as-PosS : Pos S
  ≤-as-PosS = (_≤_ , ≤-isPreorder)

  -- Part 2: Define relations Q and Q'
  Q : BinRel S Level.zero                        -- Q ⊆ U(≤)
  Q⊆U : ∀ {a b} → Q a b → U ≤-as-PosS a b

  Q' : BinRel S Level.zero                       -- Q' ⊈ U(≤)
  Q'⊈U-witness-a : S
  Q'⊈U-witness-b : S
  Q'⊈U-holds : Q' Q'⊈U-witness-a Q'⊈U-witness-b
  Q'⊈U-fails : ¬ (U ≤-as-PosS Q'⊈U-witness-a Q'⊈U-witness-b)

  -- Part 3: Show Cl(Q) ⊑ ≤ using the preorder structure on Pos(S)
  -- This means Cl-to-PosS Q is "smaller" than ≤-as-PosS in the preorder PosPreorder
  Cl-Q⊑≤ : (Cl-to-PosS Q) ⊑ ≤-as-PosS

  -- Part 4: Show Cl(Q') ⊈ ≤  
  -- This means Cl-to-PosS Q' is NOT smaller than ≤-as-PosS in the preorder
  Cl-Q'⊈≤-witness-a : S
  Cl-Q'⊈≤-witness-b : S
  Cl-Q'⊈≤-holds : U (Cl-to-PosS Q') Cl-Q'⊈≤-witness-a Cl-Q'⊈≤-witness-b
  Cl-Q'⊈≤-fails : ¬ (U ≤-as-PosS Cl-Q'⊈≤-witness-a Cl-Q'⊈≤-witness-b)
```

## Solution

**Strategy:** We'll use a concrete example with S = {1, 2, 3}:
- Choose ≤ to be the standard order: 1 ≤ 1, 1 ≤ 2, 1 ≤ 3, 2 ≤ 2, 2 ≤ 3, 3 ≤ 3
- Choose Q to be a subset: just {(1,2), (2,3)}
- Choose Q' to contain something incompatible: {(2,1)}

```agda
  -- Part 1: Standard order on {1, 2, 3}: 1 ≤ 2 ≤ 3
  _≤_ s₁ s₁ = ⊤
  _≤_ s₁ s₂ = ⊤
  _≤_ s₁ s₃ = ⊤
  _≤_ s₂ s₁ = ⊥
  _≤_ s₂ s₂ = ⊤
  _≤_ s₂ s₃ = ⊤
  _≤_ s₃ s₁ = ⊥
  _≤_ s₃ s₂ = ⊥
  _≤_ s₃ s₃ = ⊤

  -- Prove reflexivity
  ≤-refl : ∀ {a} → a ≤ a
  ≤-refl {s₁} = tt
  ≤-refl {s₂} = tt
  ≤-refl {s₃} = tt

  -- Prove transitivity
  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans {s₁} {s₁} {s₁} _ _ = tt
  ≤-trans {s₁} {s₁} {s₂} _ _ = tt
  ≤-trans {s₁} {s₁} {s₃} _ _ = tt
  ≤-trans {s₁} {s₂} {s₂} _ _ = tt
  ≤-trans {s₁} {s₂} {s₃} _ _ = tt
  ≤-trans {s₁} {s₃} {s₃} _ _ = tt
  ≤-trans {s₂} {s₂} {s₂} _ _ = tt
  ≤-trans {s₂} {s₂} {s₃} _ _ = tt
  ≤-trans {s₂} {s₃} {s₃} _ _ = tt
  ≤-trans {s₃} {s₃} {s₃} _ _ = tt

  ≤-isPreorder = record
    { reflexive = ≤-refl
    ; transitive = ≤-trans
    }

  -- Part 2: Q contains only (1,2) and (2,3) - both are in ≤
  Q s₁ s₂ = ⊤
  Q s₂ s₃ = ⊤
  Q _  _  = ⊥

  -- Proof that Q ⊆ U(≤)
  Q⊆U {s₁} {s₂} _ = tt
  Q⊆U {s₂} {s₃} _ = tt

  -- Q' contains (2,1) which is NOT in ≤ (since 2 ≰ 1)
  Q' s₂ s₁ = ⊤
  Q' _  _  = ⊥

  -- Witnesses for Q' ⊈ U(≤)
  Q'⊈U-witness-a = s₂
  Q'⊈U-witness-b = s₁
  Q'⊈U-holds = tt
  Q'⊈U-fails ()

  -- Part 3: Show Cl(Q) ⊑ ≤ using the preorder structure on Pos(S)
  -- This means ∀ {a b} → Cl Q a b → a ≤ b
  -- Since Q ⊆ U(≤) and U(≤) is already reflexive and transitive,
  -- any element built from Q via cl-refl/cl-trans is also in U(≤)
  Cl-Q⊑≤ (incl q) = Q⊆U q              -- Q a b implies U(≤) a b
  Cl-Q⊑≤ cl-refl = ≤-refl              -- U(≤) is reflexive
  Cl-Q⊑≤ (cl-trans p₁ p₂) = ≤-trans (Cl-Q⊑≤ p₁) (Cl-Q⊑≤ p₂)  -- U(≤) is transitive

  -- Part 4: We can show U(Cl-to-PosS Q') s₂ s₁ holds (since Q' s₂ s₁ holds)
  -- but U(≤-as-PosS) s₂ s₁ does not hold
  Cl-Q'⊈≤-witness-a = s₂
  Cl-Q'⊈≤-witness-b = s₁
  Cl-Q'⊈≤-holds = incl tt
  Cl-Q'⊈≤-fails ()
```

## Summary

This exercise demonstrates the Galois connection Cl ⊣ U:

- **Part 3** shows that when Q ⊆ U(≤), we have Cl(Q) ⊑ ≤. This verifies one direction of the adjunction: if the left adjoint applied to Q is below ≤, then Q must be below the right adjoint of ≤.

- **Part 4** shows that when Q' ⊈ U(≤), we have Cl(Q') ⊈ ≤. This demonstrates that the adjunction relationship genuinely depends on the subset inclusion.

Together, these illustrate the adjunction property: Cl(R) ⊑ P if and only if R ⊆ U(P).
