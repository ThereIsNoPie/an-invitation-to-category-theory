---
layout: agda
title: "Change of Base"
section: "Definitions"
chapter: 2
number: 44
---

# Change of Base

## Textbook Definition

**Construction 2.44.** Let $f : \mathcal{V} \to \mathcal{W}$ be a monoidal monotone. Given a $\mathcal{V}$-category $\mathcal{C}$, one forms the associated $\mathcal{W}$-category $\mathcal{C}_f$ as follows:

1. **Objects:** $\text{Ob}(\mathcal{C}_f) := \text{Ob}(\mathcal{C})$

2. **Hom-objects:** For any $c, d \in \text{Ob}(\mathcal{C})$, put $\mathcal{C}_f(c,d) := f(\mathcal{C}(c,d))$

### Proof that $\mathcal{C}_f$ is a $\mathcal{W}$-category

**(a) Identity axiom:** For every $c \in \mathcal{C}$:

$$I_{\mathcal{W}} \leq f(I_{\mathcal{V}}) \leq f(\mathcal{C}(c,c)) = \mathcal{C}_f(c,c)$$

where the first $\leq$ is because $f$ preserves the unit, and the second is because $f$ is monotone and $\mathcal{C}$ satisfies identity.

**(b) Composition axiom:** For every $c, d, e \in \text{Ob}(\mathcal{C})$:

$$\mathcal{C}_f(c,d) \otimes_{\mathcal{W}} \mathcal{C}_f(d,e) = f(\mathcal{C}(c,d)) \otimes_{\mathcal{W}} f(\mathcal{C}(d,e)) \leq f(\mathcal{C}(c,d) \otimes_{\mathcal{V}} \mathcal{C}(d,e)) \leq f(\mathcal{C}(c,e)) = \mathcal{C}_f(c,e)$$

where the first $\leq$ is because $f$ preserves the monoidal product, and the second is because $f$ is monotone and $\mathcal{C}$ satisfies composition.

## Agda

```agda
module definitions.chapter2.ChangeOfBase where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder; SymmetricMonoidalStructure)
open import definitions.chapter2.MonoidalMonotone
  using (MonoidalMonotone; IsMonoidalMonotone)
open import definitions.chapter2.VCategory using (VCategory)

open import Data.Product using (proj₁; proj₂)

-- Change of base construction
-- Given a monoidal monotone f : V → W and a V-category C,
-- produce the W-category C_f
changeOfBase : {V W : SymmetricMonoidalPreorder}
             → MonoidalMonotone V W
             → VCategory V
             → VCategory W
changeOfBase {V} {W} mm C = record
  { Ob = Ob
  ; hom = λ c d → f (hom c d)
  ; identity = identity-proof
  ; composition = composition-proof
  }
  where
    f = proj₁ mm
    f-is-monoidal = proj₂ mm

    open VCategory C
    open SymmetricMonoidalPreorder V
      renaming (_≤_ to _≤V_; _⊗_ to _⊗V_; I to IV)
    open SymmetricMonoidalPreorder W
      renaming (_≤_ to _≤W_; _⊗_ to _⊗W_; I to IW;
                transitive to transW; monotonicity to monoW)
    open IsMonoidalMonotone f-is-monoidal

    -- (a) Identity: IW ≤ f(IV) ≤ f(C(c,c)) = Cf(c,c)
    identity-proof : ∀ {c} → IW ≤W f (hom c c)
    identity-proof {c} = transW preserves-unit (monotone identity)

    -- (b) Composition: f(C(c,d)) ⊗W f(C(d,e)) ≤ f(C(c,d) ⊗V C(d,e)) ≤ f(C(c,e))
    composition-proof : ∀ {c d e} → (f (hom c d) ⊗W f (hom d e)) ≤W f (hom c e)
    composition-proof {c} {d} {e} =
      transW preserves-mult (monotone composition)
```
