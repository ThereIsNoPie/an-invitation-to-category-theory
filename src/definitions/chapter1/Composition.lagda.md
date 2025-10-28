---
layout: agda
title: "Composition"
section: "Definitions"
chapter: 1
number: 23
---

# Composition

**Definition 1.23.** If F : X → Y is a function and G : Y → Z is a function, their *composite* is the function X → Z defined to be G(F(x)) for any x ∈ X. It is often denoted G ◦ F, but we prefer to denote it F ; G. It takes any element x ∈ X, evaluates F to get an element F(x) ∈ Y and then evaluates G to get an element G(F(x)).

```agda
module definitions.chapter1.Composition where

-- Composition F ⨾ G of functions F : X → Y and G : Y → Z
-- Takes x ∈ X, evaluates F to get F(x) ∈ Y, then evaluates G to get G(F(x)) ∈ Z
_⨾_ : {X Y Z : Set} → (X → Y) → (Y → Z) → (X → Z)
(F ⨾ G) x = G (F x)

infixr 9 _⨾_
```
