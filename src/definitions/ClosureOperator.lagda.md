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

-- A closure operator on a preorder P is a monotone map j : P → P
-- satisfying extensivity and idempotence
record ClosureOperator (P : Preorder) : Set where
  open Preorder P

  field
    -- The closure function j : P → P
    j : Carrier → Carrier

    -- j is monotone
    j-monotonic : Monotonic _≤_ _≤_ j

    -- (a) Extensivity: p ≤ j(p) for all p ∈ P
    extensive : ∀ (p : Carrier) → p ≤ j p

    -- (b) Idempotence: j(j(p)) ≅ j(p) for all p ∈ P
    -- We use preorder equivalence (≅), not propositional equality (≡)
    idempotent : ∀ (p : Carrier) → j (j p) ≅ j p
```
