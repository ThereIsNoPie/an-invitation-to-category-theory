---
layout: agda
title: "Adjoint Functor Theorem for Preorders"
section: "Propositions"
chapter: 1
number: 108
---

# Adjoint Functor Theorem for Preorders

## Textbook Definition

**Theorem 1.108.** For preorders P and Q:
- A monotone map g : Q → P preserves meets if and only if g is a right adjoint (assuming Q has all meets)
- A monotone map f : P → Q preserves joins if and only if f is a left adjoint (assuming P has all joins)

## Agda Setup

```agda
module propositions.chapter1.AdjointFunctorTheorem where

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.GaloisConnection using (GaloisConnection)
open import definitions.chapter1.MeetJoin using (Subset; IsMeet; IsJoin; IsLowerBound; IsUpperBound)
open import definitions.chapter1.MonotoneMap using (Monotonic)
open import propositions.chapter1.AdjointsPreserveMeetsJoins using (image; right-adjoint-preserves-meets; left-adjoint-preserves-joins)
```

### Helper Definitions

```agda
-- Q has all meets
HasAllMeets : Preorder → Set₁
HasAllMeets Q = let open Preorder Q in
  ∀ (S : Subset Carrier) → ∃[ m ] IsMeet _≤_ m S

-- P has all joins
HasAllJoins : Preorder → Set₁
HasAllJoins P = let open Preorder P in
  ∀ (S : Subset Carrier) → ∃[ j ] IsJoin _≤_ j S
```

## Proposition

```agda
preserves-meets→right-adjoint : (P Q : Preorder)
                              → let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
                                    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
                                in (g : B → A)
                              → (g-mono : Monotonic (Preorder._≤_ Q) (Preorder._≤_ P) g)
                              → (all-meets : HasAllMeets Q)
                              → (preserves : ∀ (S : Subset (Preorder.Carrier Q)) (m : Preorder.Carrier Q)
                                            → IsMeet (Preorder._≤_ Q) m S
                                            → IsMeet (Preorder._≤_ P) (g m) (image g S))
                              → GaloisConnection P Q

right-adjoint→preserves-meets : (P Q : Preorder)
                              → (gc : GaloisConnection P Q)
                              → let open Preorder P renaming (_≤_ to _≤₁_)
                                    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
                                    open GaloisConnection gc
                                in ∀ (S : Subset B) (m : B) → IsMeet _≤₂_ m S
                                → IsMeet _≤₁_ (g m) (image g S)

preserves-joins→left-adjoint : (P Q : Preorder)
                             → let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
                                   open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
                               in (f : A → B)
                             → (f-mono : Monotonic (Preorder._≤_ P) (Preorder._≤_ Q) f)
                             → (all-joins : HasAllJoins P)
                             → (preserves : ∀ (S : Subset (Preorder.Carrier P)) (j : Preorder.Carrier P)
                                           → IsJoin (Preorder._≤_ P) j S
                                           → IsJoin (Preorder._≤_ Q) (f j) (image f S))
                             → GaloisConnection P Q

left-adjoint→preserves-joins : (P Q : Preorder)
                             → (gc : GaloisConnection P Q)
                             → let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
                                   open Preorder Q renaming (_≤_ to _≤₂_)
                                   open GaloisConnection gc
                               in ∀ (S : Subset A) (j : A) → IsJoin _≤₁_ j S
                               → IsJoin _≤₂_ (f j) (image f S)
```

## Proof: Part 1a (Meet Preservation → Right Adjoint)

If g : Q → P is monotone and preserves meets (and Q has all meets), then g is a right adjoint.

**Strategy:** Construct the left adjoint f by taking, for each x : A, the meet of the upper set ↑x = {q ∈ Q | x ≤ g(q)}. Verify the Galois connection using the meet-preservation property.

```agda
preserves-meets→right-adjoint P Q g g-mono all-meets preserves = record
  { f = f
  ; g = g
  ; f-g = f-g-adj
  ; g-f = g-f-adj
  }
  where
    open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- Upper set in Q corresponding to x : A
    ↑_ : A → Subset B
    ↑ x = (λ q → x ≤₁ g q)

    -- Construct left adjoint f using meets
    -- For each x : A, define f(x) = meet of { q ∈ Q | x ≤₁ g(q) }
    f : A → B
    f x = proj₁ (all-meets (↑ x))

    -- f(x) ≤₂ y → x ≤₁ g(y)
    f-g-adj : ∀ {x : A} {y : B} → f x ≤₂ y → x ≤₁ g y
    f-g-adj {x} {y} fx≤y = beginP
      x       ≤P⟨ x≤gfx ⟩
      g (f x) ≤P⟨ g-mono fx≤y ⟩
      g y     ∎P
      where
        upperset-x : Subset B
        upperset-x = ↑ x

        img-g : Subset A
        img-g = image g upperset-x

        fx-is-a-meet : IsMeet _≤₂_ (f x) upperset-x
        fx-is-a-meet = proj₂ (all-meets upperset-x)

        gfx-preserves-meet : IsMeet _≤₁_ (g (f x)) img-g
        gfx-preserves-meet = preserves upperset-x (f x) fx-is-a-meet

        x-is-lower-bound : IsLowerBound _≤₁_ x img-g
        x-is-lower-bound (q , x≤gq , refl) = x≤gq

        x≤gfx : x ≤₁ g (f x)
        x≤gfx = proj₂ gfx-preserves-meet x-is-lower-bound

    -- x ≤₁ g(y) → f(x) ≤₂ y
    g-f-adj : ∀ {x y} → x ≤₁ g y → f x ≤₂ y
    g-f-adj {x} {y} x≤gy = proj₁ fx-is-a-meet x≤gy
      where
        fx-is-a-meet : IsMeet _≤₂_ (f x) (↑ x)
        fx-is-a-meet = proj₂ (all-meets (↑ x))
```

## Proof: Part 1b (Right Adjoint → Meet Preservation)

If g is a right adjoint in a Galois connection, then g preserves meets.

**Strategy:** This is exactly Proposition 1.104.

```agda
right-adjoint→preserves-meets P Q gc S m meet-S =
  right-adjoint-preserves-meets P Q gc S m meet-S
```

## Proof: Part 2a (Join Preservation → Left Adjoint)

If f : P → Q is monotone and preserves joins (and P has all joins), then f is a left adjoint.

**Strategy:** Construct the right adjoint g by taking, for each y : B, the join of the lower set ↓y = {p ∈ P | f(p) ≤ y}. Verify the Galois connection using the join-preservation property.

```agda
preserves-joins→left-adjoint P Q f f-mono all-joins preserves = record
  { f = f
  ; g = g
  ; f-g = f-g-adj
  ; g-f = g-f-adj
  }
  where
    open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- Lower set in P corresponding to y : B
    ↓_ : B → Subset A
    ↓ y = (λ p → f p ≤₂ y)

    -- Construct right adjoint g using joins
    -- For each y : B, define g(y) = join of { p ∈ P | f(p) ≤₂ y }
    g : B → A
    g y = proj₁ (all-joins (↓ y))

    -- f(x) ≤₂ y → x ≤₁ g(y)
    f-g-adj : ∀ {x y} → f x ≤₂ y → x ≤₁ g y
    f-g-adj {x} {y} fx≤y = proj₁ gy-is-a-join fx≤y
      where
        gy-is-a-join : IsJoin _≤₁_ (g y) (↓ y)
        gy-is-a-join = proj₂ (all-joins (↓ y))

    -- x ≤₁ g(y) → f(x) ≤₂ y
    g-f-adj : ∀ {x y} → x ≤₁ g y → f x ≤₂ y
    g-f-adj {x} {y} x≤gy = beginQ
      f x     ≤Q⟨ f-mono x≤gy ⟩
      f (g y) ≤Q⟨ fgy≤y ⟩
      y       ∎Q
      where
        lowerset-y : Subset A
        lowerset-y = ↓ y

        img-f : Subset B
        img-f = image f lowerset-y

        gy-is-a-join : IsJoin _≤₁_ (g y) lowerset-y
        gy-is-a-join = proj₂ (all-joins lowerset-y)

        fgy-preserves-join : IsJoin _≤₂_ (f (g y)) img-f
        fgy-preserves-join = preserves lowerset-y (g y) gy-is-a-join

        y-is-upper-bound : IsUpperBound _≤₂_ y img-f
        y-is-upper-bound (p , fp≤y , refl) = fp≤y

        fgy≤y : f (g y) ≤₂ y
        fgy≤y = proj₂ fgy-preserves-join y-is-upper-bound
```

## Proof: Part 2b (Left Adjoint → Join Preservation)

If f is a left adjoint in a Galois connection, then f preserves joins.

**Strategy:** This is exactly Proposition 1.104.

```agda
left-adjoint→preserves-joins P Q gc S j join-S =
  left-adjoint-preserves-joins P Q gc S j join-S
```
