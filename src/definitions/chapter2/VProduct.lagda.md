---
layout: agda
title: "Product V-Categories"
section: "Definitions"
chapter: 2
number: 53
---

# Product V-Categories

## Textbook Definition

**Definition 2.51.** Let $\mathcal{X}$ and $\mathcal{Y}$ be V-categories. Define their *V-product*, or simply *product*, to be the V-category $\mathcal{X} \times \mathcal{Y}$ with:

(i) $\text{Ob}(\mathcal{X} \times \mathcal{Y}) := \text{Ob}(\mathcal{X}) \times \text{Ob}(\mathcal{Y})$

(ii) $(\mathcal{X} \times \mathcal{Y})((x, y), (x', y')) := \mathcal{X}(x, x') \otimes \mathcal{Y}(y, y')$

for two objects $(x, y)$ and $(x', y')$ in $\text{Ob}(\mathcal{X} \times \mathcal{Y})$.

## Agda Setup

```agda
module definitions.chapter2.VProduct where

open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalPreorder)
open import definitions.chapter2.VCategory using (VCategory)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; subst)
```

## Agda Formalization

```agda
-- The product of two V-categories
_×V_ : {V : SymmetricMonoidalPreorder} → VCategory V → VCategory V → VCategory V
_×V_ {V} X Y = record
  { Ob = X.Ob × Y.Ob
  ; hom = λ { (x , y) (x' , y') → X.hom x x' ⊗ Y.hom y y' }
  ; identity = identity-proof
  ; composition = composition-proof
  }
  where
    module X = VCategory X
    module Y = VCategory Y
    open SymmetricMonoidalPreorder V

    -- Identity: I ≤ X(x,x) ⊗ Y(y,y)
    -- From X: I ≤ X(x,x), From Y: I ≤ Y(y,y)
    -- Using left-unit: I = I ⊗ I ≤ X(x,x) ⊗ Y(y,y)
    identity-proof : ∀ {xy : X.Ob × Y.Ob} →
      I ≤ (X.hom (proj₁ xy) (proj₁ xy) ⊗ Y.hom (proj₂ xy) (proj₂ xy))
    identity-proof {x , y} =
      subst (_≤ (X.hom x x ⊗ Y.hom y y))
            (left-unit {I})
            (monotonicity X.identity Y.identity)

    -- Composition: (X(x₁,x₂) ⊗ Y(y₁,y₂)) ⊗ (X(x₂,x₃) ⊗ Y(y₂,y₃)) ≤ X(x₁,x₃) ⊗ Y(y₁,y₃)
    -- This requires symmetry to rearrange the terms!
    postulate
      composition-proof : ∀ {xy₁ xy₂ xy₃ : X.Ob × Y.Ob} →
        let x₁ = proj₁ xy₁; y₁ = proj₂ xy₁
            x₂ = proj₁ xy₂; y₂ = proj₂ xy₂
            x₃ = proj₁ xy₃; y₃ = proj₂ xy₃
        in ((X.hom x₁ x₂ ⊗ Y.hom y₁ y₂) ⊗ (X.hom x₂ x₃ ⊗ Y.hom y₂ y₃))
           ≤ (X.hom x₁ x₃ ⊗ Y.hom y₁ y₃)
```

## Why Symmetry is Needed

The composition proof requires rearranging:

$(X(x_1, x_2) \otimes Y(y_1, y_2)) \otimes (X(x_2, x_3) \otimes Y(y_2, y_3))$

into:

$(X(x_1, x_2) \otimes X(x_2, x_3)) \otimes (Y(y_1, y_2) \otimes Y(y_2, y_3))$

This rearrangement uses symmetry of $\otimes$ to swap the middle terms.

```agda
{-
The full proof would be:

1. Start with: (X(x₁,x₂) ⊗ Y(y₁,y₂)) ⊗ (X(x₂,x₃) ⊗ Y(y₂,y₃))

2. Use associativity and symmetry to rearrange to:
   (X(x₁,x₂) ⊗ X(x₂,x₃)) ⊗ (Y(y₁,y₂) ⊗ Y(y₂,y₃))

3. Apply monotonicity with X's composition and Y's composition:
   X(x₁,x₂) ⊗ X(x₂,x₃) ≤ X(x₁,x₃)
   Y(y₁,y₂) ⊗ Y(y₂,y₃) ≤ Y(y₁,y₃)

4. Get: X(x₁,x₃) ⊗ Y(y₁,y₃)
-}
```
