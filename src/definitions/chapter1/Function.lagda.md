---
layout: agda
title: "Function"
section: "Definitions"
chapter: 1
number: 17
---

# Function

**Definition 1.17.** Let S and T be sets. A *function from S to T* is a subset F ⊆ S × T such that for all s ∈ S, there exists a unique t ∈ T with (s, t) ∈ F.

The function F is often denoted F : S → T. From now on, we write F(s) = t, or sometimes s ↦ t, to mean (s, t) ∈ F. For any t ∈ T, the *preimage of t along F* is the subset F⁻¹(t) := {s ∈ S | F(s) = t}.

A function is called *surjective*, or a *surjection*, if for all t ∈ T, there exists s ∈ S with F(s) = t. A function is called *injective*, or an *injection*, if for all t ∈ T and s₁, s₂ ∈ S with F(s₁) = t and F(s₂) = t, we have s₁ = s₂. A function is called *bijective* if it is both surjective and injective.

```agda
module definitions.chapter1.Function where

open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import definitions.chapter1.Partition using (Subset)

-- Preimage of t along F
Preimage : {S T : Set} → (S → T) → T → Subset S
Preimage F t = λ s → F s ≡ t

-- A function F : S → T is surjective if for all t ∈ T,
-- there exists s ∈ S with F(s) = t
Surjective : {S T : Set} → (S → T) → Set
Surjective {S} {T} F = ∀ (t : T) → Σ[ s ∈ S ] (F s ≡ t)

-- A function F : S → T is injective if for all s₁, s₂ ∈ S
-- with F(s₁) = t and F(s₂) = t, we have s₁ = s₂
Injective : {S T : Set} → (S → T) → Set
Injective {S} F = ∀ {s₁ s₂ : S} → F s₁ ≡ F s₂ → s₁ ≡ s₂

-- A function is bijective if it is both surjective and injective
Bijective : {S T : Set} → (S → T) → Set
Bijective F = Surjective F × Injective F
  where open import Data.Product using (_×_)
```
