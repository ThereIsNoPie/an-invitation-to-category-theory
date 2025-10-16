---
layout: agda
title: "Galois Theorems"
section: "Exercises"
chapter: 1
number: 101
subsections:
  - name: "Prop 1.101"
    chapter: 1
    number: 101
    anchor: "GaloisTheorems.FromGalois"
  - name: "Prop 1.104"
    chapter: 1
    number: 104
    anchor: "GaloisTheorems.Prop104"
  - name: "Theorem 1.108"
    chapter: 1
    number: 108
    anchor: "GaloisTheorems.Theorem108"
---

```agda
module exercises.GaloisTheorems where

open import definitions.Preorder
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Proposition 1.101: Equivalence between Galois connection and unit/counit conditions
module GaloisTheorems (P Q : Preorder) where
  open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)

  -- Forward direction: Galois connection implies unit/counit conditions
  module FromGalois (gc : GaloisConnection P Q) where
    open GaloisConnection gc
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- p ≤ g(f(p)) for all p
    unit : ∀ (p : A) → p ≤₁ g (f p)
    unit p = beginP
      p       ≤P⟨ f-g lem ⟩
      g (f p) ∎P
      where
        lem : f p ≤₂ f p
        lem = f p ∎Q

    -- f(g(q)) ≤ q for all q
    counit : ∀ (q : B) → f (g q) ≤₂ q
    counit q = beginQ
      f (g q) ≤Q⟨ g-f lem ⟩
      q       ∎Q
      where
        lem : g q ≤₁ g q
        lem = g q ∎P

  -- Backward direction: unit/counit conditions imply Galois connection
  module ToGalois (f : A → B) (g : B → A)
                  (f-mono : Monotonic _≤₁_ _≤₂_ f)
                  (g-mono : Monotonic _≤₂_ _≤₁_ g)
                  (unit : ∀ (p : A) → p ≤₁ g (f p))
                  (counit : ∀ (q : B) → f (g q) ≤₂ q) where

    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- f(x) ≤ y → x ≤ g(y)
    f-g-adj : ∀ {x y} → f x ≤₂ y → x ≤₁ g y
    f-g-adj {x} {y} fx≤y = beginP
      x       ≤P⟨ unit x ⟩
      g (f x) ≤P⟨ g-mono fx≤y ⟩
      g y     ∎P

    -- x ≤ g(y) → f(x) ≤ y
    g-f-adj : ∀ {x y} → x ≤₁ g y → f x ≤₂ y
    g-f-adj {x} {y} x≤gy = beginQ
      f x     ≤Q⟨ f-mono x≤gy ⟩
      f (g y) ≤Q⟨ counit y ⟩
      y       ∎Q

    galoisConnection : GaloisConnection P Q
    galoisConnection = record
      { f = f
      ; g = g
      ; f-g = f-g-adj
      ; g-f = g-f-adj
      }

  -- Proposition 1.104: Right adjoints preserve meets, left adjoints preserve joins
  module Prop104 (gc : GaloisConnection P Q) where
    open GaloisConnection gc
    open MeetJoin
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- Image of a subset under a function
    image : {X Y : Set} → (X → Y) → Subset X → Subset Y
    image h S y = ∃[ x ] (S x × h x ≡ y)

    -- Right adjoints preserve meets: g(∧A) ∼= ∧g(A)
    module RightAdjointPreservesMeet (S : Subset B) (m : B) (meet-S : IsMeet _≤₂_ m S) where

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

      g-preserves-meet : IsMeet _≤₁_ (g m) (image g S)
      g-preserves-meet = g-lower-bound , g-greatest-lower

    -- Left adjoints preserve joins: f(∨A) ∼= ∨f(A)
    module LeftAdjointPreserveJoin (S : Subset A) (j : A) (join-S : IsJoin _≤₁_ j S) where

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
          open FromGalois gc
          lem : j ≤₁ g y
          lem = proj₂ join-S λ {p} Sp → beginP
            p       ≤P⟨ unit p ⟩
            g (f p) ≤P⟨ g-monotonic (y-upper (p , Sp , refl)) ⟩
            g y     ∎P

      f-preserves-join : IsJoin _≤₂_ (f j) (image f S)
      f-preserves-join = f-upper-bound , f-least-upper

  -- Theorem 1.108: Adjoint Functor Theorem for Preorders
  module Theorem108 where
    open MeetJoin

    image : {X Y : Set} → (X → Y) → Subset X → Subset Y
    image h S y = ∃[ x ] (S x × h x ≡ y)

    -- Q has all meets
    HasAllMeets : Preorder → Set₁
    HasAllMeets Q' = let open Preorder Q' in
      ∀ (S : Subset Carrier) → ∃[ m ] IsMeet _≤_ m S

    -- P has all joins
    HasAllJoins : Preorder → Set₁
    HasAllJoins P' = let open Preorder P' in
      ∀ (S : Subset Carrier) → ∃[ j ] IsJoin _≤_ j S

    -- Part 1: g : Q → P preserves meets iff g is a right adjoint (assuming Q has all meets)
    module RightAdjoint (g : B → A) where
      -- g preserves meets means: for all subsets S and their meet m, g(m) is the meet of g(S)
      PreservesMeets : Set₁
      PreservesMeets = ∀ (S : Subset B) (m : B) → IsMeet _≤₂_ m S → IsMeet _≤₁_ (g m) (image g S)

      ↑_ : A → Subset B
      ↑ x = (λ q → x ≤₁ g q)

      -- Forward direction: if g preserves meets, then g is a right adjoint
      preserves-meets→is-right-adjoint : HasAllMeets Q → Monotonic _≤₂_ _≤₁_ g →
        PreservesMeets → GaloisConnection P Q
      preserves-meets→is-right-adjoint all-meets g-mono pres = record
        { f = f
        ; g = g
        ; f-g = f-g-adj
        ; g-f = g-f-adj
        }
        where
          open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
          open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

          -- Construct left adjoint f using meets
          -- For each x : A, define f(x) = meet of { q ∈ Q | x ≤₁ g(q) }
          f : A → B
          f x = proj₁ (all-meets (↑ x))

          -- f(x) ≤₂ y → x ≤₁ g(y)
          f-g-adj : ∀ {x : A}  {y : B} → f x ≤₂ y → x ≤₁ g y
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
              gfx-preserves-meet = pres upperset-x (f x) fx-is-a-meet

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

      -- Backward direction: if g is a right adjoint, then g preserves meets
      -- This is exactly what Prop104.RightAdjointPreservesMeet proves!
      is-right-adjoint→preserves-meets : (gc : GaloisConnection P Q) →
        GaloisConnection.g gc ≡ g → PreservesMeets
      is-right-adjoint→preserves-meets gc refl S m meet-S =
        Prop104.RightAdjointPreservesMeet.g-preserves-meet gc S m meet-S

    -- Part 2: f : P → Q preserves joins iff f is a left adjoint (assuming P has all joins)
    module LeftAdjoint (f : A → B) where

      -- f preserves joins means: for all subsets S and their join j, f(j) is the join of f(S)
      PreservesJoins : Set₁
      PreservesJoins = ∀ (S : Subset A) (j : A) → IsJoin _≤₁_ j S → IsJoin _≤₂_ (f j) (image f S)

      ↓_ : B → Subset A
      ↓ y = (λ p → f p ≤₂ y)

      -- Forward direction: if f preserves joins, then f is a left adjoint
      preserves-joins→is-left-adjoint : HasAllJoins P → Monotonic _≤₁_ _≤₂_ f →
        PreservesJoins → GaloisConnection P Q
      preserves-joins→is-left-adjoint all-joins f-mono pres = record
        { f = f
        ; g = g
        ; f-g = f-g-adj
        ; g-f = g-f-adj
        }
        where
          open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
          open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

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
              fgy-preserves-join = pres lowerset-y (g y) gy-is-a-join

              y-is-upper-bound : IsUpperBound _≤₂_ y img-f
              y-is-upper-bound (p , fp≤y , refl) = fp≤y

              fgy≤y : f (g y) ≤₂ y
              fgy≤y = proj₂ fgy-preserves-join y-is-upper-bound

      -- Backward direction: if f is a left adjoint, then f preserves joins
      -- This is exactly what Prop104.LeftAdjointPreserveJoin proves!
      is-left-adjoint→preserves-joins : (gc : GaloisConnection P Q) →
        GaloisConnection.f gc ≡ f → PreservesJoins
      is-left-adjoint→preserves-joins gc refl S j join-S =
        Prop104.LeftAdjointPreserveJoin.f-preserves-join gc S j join-S
```
