---
layout: agda
title: "Galois Connection Unit-Counit Characterization"
section: "Propositions"
chapter: 1
number: 101
---

# Galois Connection Unit-Counit Characterization

## Textbook Definition

**Proposition 1.101.** A pair of monotone maps f : P → Q and g : Q → P forms a Galois connection if and only if they satisfy the unit and counit conditions:
- Unit: p ≤ g(f(p)) for all p ∈ P
- Counit: f(g(q)) ≤ q for all q ∈ Q

## Agda Setup

```agda
module propositions.chapter1.GaloisUnitCounit where

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.GaloisConnection using (GaloisConnection)
open import definitions.chapter1.MonotoneMap using (Monotonic)
```

## Proposition

```agda
galois→unit-counit : (P Q : Preorder)
                   → (gc : GaloisConnection P Q)
                   → let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
                         open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
                         open GaloisConnection gc
                     in ((∀ (p : A) → p ≤₁ g (f p)) × (∀ (q : B) → f (g q) ≤₂ q))

unit-counit→galois : (P Q : Preorder)
                   → let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
                         open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
                     in (f : A → B) → (g : B → A)
                   → (f-mono : Monotonic (Preorder._≤_ P) (Preorder._≤_ Q) f)
                   → (g-mono : Monotonic (Preorder._≤_ Q) (Preorder._≤_ P) g)
                   → (unit : ∀ (p : Preorder.Carrier P) → Preorder._≤_ P p (g (f p)))
                   → (counit : ∀ (q : Preorder.Carrier Q) → Preorder._≤_ Q (f (g q)) q)
                   → GaloisConnection P Q
```

## Proof: Part 1 (Galois Connection → Unit and Counit)

If f ⊣ g is a Galois connection, then the unit and counit conditions hold.

**Strategy:** Use the Galois connection property with reflexivity. For unit, apply f(p) ≤ f(p) to get p ≤ g(f(p)). For counit, apply g(q) ≤ g(q) to get f(g(q)) ≤ q.

```agda
galois→unit-counit P Q gc = (unit , counit)
  where
    open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
    open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
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
```

## Proof: Part 2 (Unit and Counit → Galois Connection)

If f and g are monotone maps satisfying the unit and counit conditions, then they form a Galois connection.

**Strategy:** Given f(x) ≤ y, compose with the unit to get x ≤ g(f(x)) and use monotonicity of g to get x ≤ g(y). Given x ≤ g(y), use monotonicity of f to get f(x) ≤ f(g(y)) and compose with counit to get f(x) ≤ y.

```agda
unit-counit→galois P Q f g f-mono g-mono unit counit = record
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
```
