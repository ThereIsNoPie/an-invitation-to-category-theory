---
layout: agda
title: "Closure Operator"
section: "Definitions"
chapter: 1
number: 112
---

# Closure Operator

**Definition 1.112.** A *closure operator* j : P → P on a preorder P is a monotone map such that for all p ∈ P we have

(a) p ≤ j(p),

(b) j(j(p)) ≅ j(p).

```agda
module definitions.ClosureOperator where

open import definitions.Preorder using (Preorder)
open import definitions.MonotoneMap using (Monotonic)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- A closure operator on a preorder P is a monotone map j : P → P
-- satisfying extensivity and idempotence
record ClosureOperator (P : Preorder) : Set where
  open Preorder P renaming (Carrier to A; _≤_ to _≤P_)

  field
    -- The closure function j : P → P
    j : A → A

    -- j is monotone
    j-monotonic : Monotonic _≤P_ _≤P_ j

    -- (a) Extensivity: p ≤ j(p) for all p ∈ P
    extensive : ∀ (p : A) → p ≤P j p

    -- (b) Idempotence: j(j(p)) ≅ j(p) for all p ∈ P
    -- This means j(j(p)) ≤ j(p) and j(p) ≤ j(j(p))
    idempotent : ∀ (p : A) → j (j p) ≡ j p
```
