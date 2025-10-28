---
layout: agda
title: "Adjoints Preserve Meets and Joins"
section: "Propositions"
chapter: 1
number: 104
---

# Adjoints Preserve Meets and Joins

## Textbook Definition

**Proposition 1.104.** In a Galois connection f ⊣ g between preorders P and Q:
- Right adjoints preserve meets: g(∧B) is the meet of g(B) for any subset B ⊆ Q
- Left adjoints preserve joins: f(∨A) is the join of f(A) for any subset A ⊆ P

## Agda Setup

```agda
module propositions.chapter1.AdjointsPreserveMeetsJoins where

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.GaloisConnection using (GaloisConnection)
open import definitions.chapter1.MeetJoin using (Subset; IsMeet; IsJoin; IsLowerBound; IsUpperBound)
open import propositions.chapter1.GaloisUnitCounit using (galois→unit-counit)
```

### Helper: Image of a Subset

```agda
-- Image of a subset under a function
image : {X Y : Set} → (X → Y) → Subset X → Subset Y
image h S y = ∃[ x ] (S x × h x ≡ y)
```

## Proposition

```agda
right-adjoint-preserves-meets : (P Q : Preorder)
                              → (gc : GaloisConnection P Q)
                              → let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
                                    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
                                    open GaloisConnection gc
                                in (S : Subset B) → (m : B) → IsMeet _≤₂_ m S
                                → IsMeet _≤₁_ (g m) (image g S)

left-adjoint-preserves-joins : (P Q : Preorder)
                             → (gc : GaloisConnection P Q)
                             → let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
                                   open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
                                   open GaloisConnection gc
                               in (S : Subset A) → (j : A) → IsJoin _≤₁_ j S
                               → IsJoin _≤₂_ (f j) (image f S)
```

## Proof: Part 1 (Right Adjoints Preserve Meets)

If g is the right adjoint in a Galois connection and m is the meet of a subset S ⊆ Q, then g(m) is the meet of g(S).

**Strategy:** Show that g(m) is a lower bound for g(S) using monotonicity, and that it's the greatest lower bound using the Galois connection adjunction.

```agda
right-adjoint-preserves-meets P Q gc S m meet-S = (g-lower-bound , g-greatest-lower)
  where
    open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
    open GaloisConnection gc
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- g(m) is a lower bound for g(S)
    g-lower-bound : IsLowerBound _≤₁_ (g m) (image g S)
    g-lower-bound {p} (q , Sq , refl) = beginP
      g m ≤P⟨ g-monotonic (proj₁ meet-S Sq) ⟩
      g q ∎P

    -- g(m) is the greatest lower bound for g(S)
    g-greatest-lower : ∀ {x} → IsLowerBound _≤₁_ x (image g S) → x ≤₁ g m
    g-greatest-lower {x} x-lower = beginP
      x     ≤P⟨ f-g lem ⟩
      g m   ∎P
      where
        lem : f x ≤₂ m
        lem = proj₂ meet-S λ {q} Sq → g-f (x-lower (q , Sq , refl))
```

## Proof: Part 2 (Left Adjoints Preserve Joins)

If f is the left adjoint in a Galois connection and j is the join of a subset S ⊆ P, then f(j) is the join of f(S).

**Strategy:** Show that f(j) is an upper bound for f(S) using monotonicity, and that it's the least upper bound using the Galois connection adjunction and the unit condition.

```agda
left-adjoint-preserves-joins P Q gc S j join-S = (f-upper-bound , f-least-upper)
  where
    open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
    open GaloisConnection gc
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    unit : ∀ (p : A) → p ≤₁ g (f p)
    unit = proj₁ (galois→unit-counit P Q gc)

    -- f(j) is an upper bound for f(S)
    f-upper-bound : IsUpperBound _≤₂_ (f j) (image f S)
    f-upper-bound {q} (p , Sp , refl) = beginQ
      f p ≤Q⟨ f-monotonic (proj₁ join-S Sp) ⟩
      f j ∎Q

    -- f(j) is the least upper bound for f(S)
    f-least-upper : ∀ {y} → IsUpperBound _≤₂_ y (image f S) → f j ≤₂ y
    f-least-upper {y} y-upper = beginQ
      f j ≤Q⟨ g-f lem ⟩
      y   ∎Q
      where
        lem : j ≤₁ g y
        lem = proj₂ join-S λ {p} Sp → beginP
          p       ≤P⟨ unit p ⟩
          g (f p) ≤P⟨ g-monotonic (y-upper (p , Sp , refl)) ⟩
          g y     ∎P
```
