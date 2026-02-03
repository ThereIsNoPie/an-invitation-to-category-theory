---
layout: agda
title: "Monoidal Monotone"
section: "Definitions"
chapter: 2
number: 25
---

# Monoidal Monotone

## Textbook Definition

**Definition 2.25.** Let P = (P, ≤_P, I_P, ⊗_P) and Q = (Q, ≤_Q, I_Q, ⊗_Q) be monoidal preorders. A **monoidal monotone** from P to Q is a monotone map f : (P, ≤_P) → (Q, ≤_Q), satisfying two conditions:

(a) I_Q ≤_Q f(I_P),

(b) f(p₁) ⊗_Q f(p₂) ≤_Q f(p₁ ⊗_P p₂)

for all p₁, p₂ ∈ P.

There are strengthenings of these conditions that are also important. If f satisfies the following conditions, it is called a **strong monoidal monotone**:

(a′) I_Q ≅ f(I_P),

(b′) f(p₁) ⊗_Q f(p₂) ≅ f(p₁ ⊗_P p₂);

and if it satisfies the following conditions it is called a **strict monoidal monotone**:

(a′′) I_Q = f(I_P),

(b′′) f(p₁) ⊗_Q f(p₂) = f(p₁ ⊗_P p₂).

## Agda Formalization

```agda
module definitions.chapter2.MonoidalMonotone where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.MonotoneMap using (Monotonic; _⇒_)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- A monoidal monotone from P to Q is a monotone map f : (P, ≤P) → (Q, ≤Q)
-- satisfying two conditions relating to the monoidal structure
record IsMonoidalMonotone
  (P Q : SymmetricMonoidalPreorder)
  (f : SymmetricMonoidalPreorder.Carrier P →
       SymmetricMonoidalPreorder.Carrier Q)
  : Set where

  open SymmetricMonoidalPreorder P renaming
    ( Carrier to P-Carrier
    ; _≤_ to _≤P_
    ; _≅_ to _≅P_
    ; I to I-P
    ; _⊗_ to _⊗P_
    )
  open SymmetricMonoidalPreorder Q renaming
    ( Carrier to Q-Carrier
    ; _≤_ to _≤Q_
    ; _≅_ to _≅Q_
    ; I to I-Q
    ; _⊗_ to _⊗Q_
    ; reflexive to reflexive-Q
    )

  field
    -- f must be monotone
    monotone : Monotonic _≤P_ _≤Q_ f

    -- (a) I_Q ≤_Q f(I_P)
    preserves-unit : I-Q ≤Q f I-P

    -- (b) f(p₁) ⊗_Q f(p₂) ≤_Q f(p₁ ⊗_P p₂) for all p₁, p₂ ∈ P
    preserves-mult : ∀ {p₁ p₂ : P-Carrier} →
                     (f p₁ ⊗Q f p₂) ≤Q f (p₁ ⊗P p₂)

-- A monoidal monotone: a pair of a function and a proof it is monoidal monotone
MonoidalMonotone : SymmetricMonoidalPreorder → SymmetricMonoidalPreorder → Set
MonoidalMonotone P Q =
  Σ[ f ∈ (SymmetricMonoidalPreorder.Carrier P →
          SymmetricMonoidalPreorder.Carrier Q) ]
  (IsMonoidalMonotone P Q f)

-- Strong monoidal monotone: uses ≅ (equivalence) instead of ≤
-- This is a strengthening of monoidal monotone
record IsStrongMonoidalMonotone
  (P Q : SymmetricMonoidalPreorder)
  (f : SymmetricMonoidalPreorder.Carrier P →
       SymmetricMonoidalPreorder.Carrier Q)
  : Set where

  open SymmetricMonoidalPreorder P renaming
    ( Carrier to P-Carrier
    ; _≤_ to _≤P_
    ; _≅_ to _≅P_
    ; I to I-P
    ; _⊗_ to _⊗P_
    )
  open SymmetricMonoidalPreorder Q renaming
    ( Carrier to Q-Carrier
    ; _≤_ to _≤Q_
    ; _≅_ to _≅Q_
    ; I to I-Q
    ; _⊗_ to _⊗Q_
    )

  field
    -- f must be monotone
    monotone : Monotonic _≤P_ _≤Q_ f

    -- (a′) I_Q ≅ f(I_P)
    preserves-unit-≅ : I-Q ≅Q f I-P

    -- (b′) f(p₁) ⊗_Q f(p₂) ≅ f(p₁ ⊗_P p₂) for all p₁, p₂ ∈ P
    preserves-mult-≅ : ∀ {p₁ p₂ : P-Carrier} →
                       (f p₁ ⊗Q f p₂) ≅Q f (p₁ ⊗P p₂)

  -- Derive lax monoidal monotone (≅ means both ≤ and ≥, so take first projection)
  is-monoidal-monotone : IsMonoidalMonotone P Q f
  is-monoidal-monotone = record
    { monotone = monotone
    ; preserves-unit = proj₁ preserves-unit-≅
    ; preserves-mult = proj₁ preserves-mult-≅
    }

StrongMonoidalMonotone : SymmetricMonoidalPreorder → SymmetricMonoidalPreorder → Set
StrongMonoidalMonotone P Q =
  Σ[ f ∈ (SymmetricMonoidalPreorder.Carrier P →
          SymmetricMonoidalPreorder.Carrier Q) ]
  (IsStrongMonoidalMonotone P Q f)

-- Strict monoidal monotone: uses = (equality) instead of ≤
-- This is the strongest form
record IsStrictMonoidalMonotone
  (P Q : SymmetricMonoidalPreorder)
  (f : SymmetricMonoidalPreorder.Carrier P →
       SymmetricMonoidalPreorder.Carrier Q)
  : Set where

  open SymmetricMonoidalPreorder P renaming
    ( Carrier to P-Carrier
    ; _≤_ to _≤P_
    ; _≅_ to _≅P_
    ; I to I-P
    ; _⊗_ to _⊗P_
    )
  open SymmetricMonoidalPreorder Q renaming
    ( Carrier to Q-Carrier
    ; _≤_ to _≤Q_
    ; _≅_ to _≅Q_
    ; I to I-Q
    ; _⊗_ to _⊗Q_
    ; reflexive to reflexive-Q
    )

  field
    -- f must be monotone
    monotone : Monotonic _≤P_ _≤Q_ f

    -- (a′′) I_Q = f(I_P)
    preserves-unit-≡ : I-Q ≡ f I-P

    -- (b′′) f(p₁) ⊗_Q f(p₂) = f(p₁ ⊗_P p₂) for all p₁, p₂ ∈ P
    preserves-mult-≡ : ∀ {p₁ p₂ : P-Carrier} →
                       (f p₁ ⊗Q f p₂) ≡ f (p₁ ⊗P p₂)

  -- Helper: equality implies equivalence
  ≡-to-≅ : ∀ {x y : Q-Carrier} → x ≡ y → x ≅Q y
  ≡-to-≅ refl = (reflexive-Q , reflexive-Q)

  -- Derive strong monoidal monotone (≡ implies ≅)
  is-strong-monoidal-monotone : IsStrongMonoidalMonotone P Q f
  is-strong-monoidal-monotone = record
    { monotone = monotone
    ; preserves-unit-≅ = ≡-to-≅ preserves-unit-≡
    ; preserves-mult-≅ = ≡-to-≅ preserves-mult-≡
    }

  -- Derive lax monoidal monotone (via strong)
  is-monoidal-monotone : IsMonoidalMonotone P Q f
  is-monoidal-monotone =
    IsStrongMonoidalMonotone.is-monoidal-monotone is-strong-monoidal-monotone

StrictMonoidalMonotone : SymmetricMonoidalPreorder → SymmetricMonoidalPreorder → Set
StrictMonoidalMonotone P Q =
  Σ[ f ∈ (SymmetricMonoidalPreorder.Carrier P →
          SymmetricMonoidalPreorder.Carrier Q) ]
  (IsStrictMonoidalMonotone P Q f)
```

## Notes

The three variants form a hierarchy with automatic coercions:

- **Monoidal monotone** (lax): Preserves structure up to ≤ (weakest)
- **Strong monoidal monotone**: Preserves structure up to ≅ (isomorphism), derives lax via `is-monoidal-monotone`
- **Strict monoidal monotone**: Preserves structure on the nose via = (strongest), derives both strong and lax

The code structure mirrors the mathematical hierarchy:
- `IsStrongMonoidalMonotone` provides `is-monoidal-monotone : IsMonoidalMonotone`
- `IsStrictMonoidalMonotone` provides both `is-strong-monoidal-monotone : IsStrongMonoidalMonotone` and `is-monoidal-monotone : IsMonoidalMonotone`

This means if you have a strict monoidal monotone, you automatically get the weaker versions without additional proof work. In the special case where the preorders are discrete (x ≤ y iff x = y), all three notions coincide.
```
