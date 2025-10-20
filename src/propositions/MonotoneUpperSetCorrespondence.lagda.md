---
layout: agda
title: "Monotone-UpperSet Correspondence"
section: "Propositions"
chapter: 1
number: 73
---

# Monotone-UpperSet Correspondence

## Textbook Definition

**Proposition 1.73.** Let P be a preorder. Monotone maps P → B are in one-to-one correspondence with upper sets of P.

## Intuition

The two-element preorder B has elements {false, true} with false ≤ true. An upper set is a subset that is "upward closed": if x is in the set and x ≤ y, then y is also in the set.

The correspondence is:
- **Monotone → Upper Set:** Given f : P → B, the upper set is {x ∈ P | f(x) = true}
- **Upper Set → Monotone:** Given upper set U, define f(x) = true if x ∈ U, false otherwise

## Agda Setup

```agda
module propositions.MonotoneUpperSetCorrespondence where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_; Σ; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)

open import definitions.Preorder using (Preorder; IsPreorder)
open import definitions.MonotoneMap using (Monotonic; _⇒_)

-- Subset type
Subset : Set → Set₁
Subset A = A → Set
```

### The Two-Element Preorder B

B has two elements: false and true, with the ordering false ≤ true.

```agda
-- The ordering on Bool: false ≤ true
data _≤B_ : Bool → Bool → Set where
  false≤false : false ≤B false
  false≤true  : false ≤B true
  true≤true   : true ≤B true

-- B is a preorder
B-isPreorder : IsPreorder _≤B_
B-isPreorder = record
  { reflexive = λ {x} → reflexive-proof x
  ; transitive = λ {x} {y} {z} → transitive-proof x y z
  }
  where
    reflexive-proof : ∀ x → x ≤B x
    reflexive-proof false = false≤false
    reflexive-proof true = true≤true

    transitive-proof : ∀ x y z → x ≤B y → y ≤B z → x ≤B z
    transitive-proof false false false false≤false false≤false = false≤false
    transitive-proof false false true false≤false false≤true = false≤true
    transitive-proof false true true false≤true true≤true = false≤true
    transitive-proof true true true true≤true true≤true = true≤true

-- The preorder B
B : Preorder
B = record
  { Carrier = Bool
  ; _≤_ = _≤B_
  ; isPreorder = B-isPreorder
  }
```

### Upper Sets

An upper set (or upward closed set) is a subset U such that if x ∈ U and x ≤ y, then y ∈ U.

```agda
-- A subset U is an upper set if it's upward closed
IsUpperSet : {A : Set} → (_≤_ : A → A → Set) → Subset A → Set
IsUpperSet _≤_ U = ∀ {x y} → U x → x ≤ y → U y

-- The type of upper sets of a preorder
UpperSet : Preorder → Set₁
UpperSet P = Σ[ U ∈ Subset (Preorder.Carrier P) ] (IsUpperSet (Preorder._≤_ P) U)
```

## Proposition

```agda
monotone→upperset : (P : Preorder) → (P ⇒ B) → UpperSet P

upperset→monotone : (P : Preorder) → UpperSet P → (P ⇒ B)
```

## Proof: Direction 1 (Monotone Map → Upper Set)

Given a monotone map f : P → B, we extract the upper set U = {x ∈ P | f(x) = true}.

**Strategy:** The preimage of true is upward closed because f is monotone.

```agda
monotone→upperset P (f , f-mono) = U , U-is-upper
  where
    open Preorder P renaming (Carrier to A; _≤_ to _≤P_)

    -- The upper set is the preimage of true
    U : Subset A
    U x = f x ≡ true

    -- Prove U is upward closed
    U-is-upper : IsUpperSet _≤P_ U
    U-is-upper {x} {y} fx≡true x≤y with f x | f y | f-mono x≤y
    ... | true | true | true≤true = refl
    ... | true | false | ()
```

## Proof: Direction 2 (Upper Set → Monotone Map)

Given an upper set U ⊆ P, we define f : P → B by f(x) = true if x ∈ U, false otherwise.

**Strategy:** Use the Law of Excluded Middle to decide membership in U. If x ≤ y and f(x) = true, then x ∈ U, so y ∈ U (by upward closure), hence f(y) = true.

```agda
upperset→monotone P (U , U-is-upper) = f , f-mono
  where
    open Preorder P renaming (Carrier to A; _≤_ to _≤P_)
    open import plumbing.ClassicalPostulates using (LEM)

    -- Define f : P → Bool using LEM to decide membership
    f : A → Bool
    f x with LEM {U x}
    ... | inj₁ _ = true
    ... | inj₂ _ = false

    -- Prove f is monotone
    f-mono : Monotonic _≤P_ _≤B_ f
    f-mono {x} {y} x≤y with LEM {U x} | LEM {U y}
    ... | inj₁ x∈U | inj₁ y∈U = true≤true
    ... | inj₁ x∈U | inj₂ y∉U = ⊥-elim (y∉U (U-is-upper x∈U x≤y))
    ... | inj₂ x∉U | inj₁ y∈U = false≤true
    ... | inj₂ x∉U | inj₂ y∉U = false≤false
```

## Proof: Roundtrip Properties

We can show that these maps are inverses of each other (up to equivalence).

```agda
-- Going from monotone map to upper set and back preserves the upper set
roundtrip-1 : (P : Preorder) → (f : P ⇒ B) →
  ∀ x → proj₁ (monotone→upperset P f) x ≡ (proj₁ f x ≡ true)
roundtrip-1 P (f , f-mono) x = refl
```
