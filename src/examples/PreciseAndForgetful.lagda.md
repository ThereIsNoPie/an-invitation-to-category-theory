---
layout: agda
title: "Precise and Forgetful Example"
section: "Examples"
---

# Precise and Forgetful

Agda allows you to be **precise** and **forgetful**.

Here's the original textbook proposition.

## Proposition 1.104 (Right adjoints preserve meets)
```markdown
**Proposition 1.104.** Let f : P → Q be left adjoint to g : Q → P. Suppose that A ⊆ Q is any subset, and let g(A) := {g(a) | a ∈ A} be its image. Then if A has a meet ⋀ A ∈ Q then g(A) has a meet ⋀ g(A) in P, and we have

g(⋀ A) ≅ ⋀ g(A).

That is, right adjoints preserve meets. Similarly, left adjoints preserve joins: if A ⊆ P is any subset that has a join ⋁ A ∈ P, then f(A) has a join ⋁ f(A) in Q, and we have

f(⋁ A) ≅ ⋁ f(A).
```

---

There's a lot of definitions. It's easy to forget what they mean. 

<!--
```agda
module examples.PreciseAndForgetful where

open import definitions.Preorder
open import definitions.GaloisConnection using (GaloisConnection)
open import definitions.MeetJoin
open import Data.Product using (∃-syntax; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

```
-->

Here's the same proposition in Agda

```agda
module RightAdjointExample (P Q : Preorder) (gc : GaloisConnection P Q) where
  open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
  open GaloisConnection gc

  -- Image of a subset under a function
  image : {X Y : Set} → (X → Y) → Subset X → Subset Y
  image h S y = ∃[ x ] (S x × h x ≡ y)

  module RightAdjointPreservesMeet (S : Subset B) (m : B) (meet-S : IsMeet _≤₂_ m S) where

    -- g(m) is a lower bound for g(S)
    postulate
      g-lower-bound : IsLowerBound _≤₁_ (g m) (image g S)

    -- g(m) is the greatest lower bound for g(S)
    postulate
      g-greatest-lower : ∀ {x} → IsLowerBound _≤₁_ x (image g S) → x ≤₁ g m

    -- Therefore g(m) is the meet of g(S)
    postulate
      g-preserves-meet : IsMeet _≤₁_ (g m) (image g S)
```

* Click on any term to see its definition. 
* You'll always remember what you have access to. 
* If you try to implement a proof, Agda will tell you **precisely** what you need to prove. 
* If you make a mistake, Agda will tell you **precisely** where you went wrong.

See the [full proof with implementations](../exercises/GaloisTheorems.html#exercises.GaloisTheorems.Prop104.RightAdjointPreservesMeet) for how these postulates are actually proved.
