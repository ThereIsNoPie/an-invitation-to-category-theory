---
layout: agda
title: "Graph"
section: "Definitions"
chapter: 1
number: 31
---

# Graph

**Definition 1.31.** A *graph* G = (V, A, s, t) consists of a set V whose elements are called *vertices*, a set A whose elements are called *arrows*, and two functions s, t : A → V known as the *source* and *target* functions respectively. Given a ∈ A with s(a) = v and t(a) = w, we say that a is an *arrow from v to w*.

By a *path* in G we mean any sequence of arrows such that the target of one arrow is the source of the next. This includes sequences of length 1, which are just arrows a ∈ A in G, and sequences of length 0, which just start and end at the same vertex v, without traversing any arrows.

```agda
module definitions.chapter1.Graph where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- A graph G = (V, A, s, t) consists of vertices V, arrows A,
-- and source and target functions s, t : A → V
record Graph : Set₁ where
  field
    V : Set  -- Vertices
    A : Set  -- Arrows
    s : A → V  -- Source function
    t : A → V  -- Target function

-- A path in G is a sequence of arrows where the target of one arrow
-- is the source of the next
data Path (G : Graph) : Graph.V G → Graph.V G → Set where
  -- Length 0: empty path from v to v
  []  : ∀ {v} → Path G v v

  -- Length ≥ 1: cons an arrow onto a path
  _∷_ : ∀ {v w u} → (a : Graph.A G)
      → Graph.s G a ≡ v
      → Graph.t G a ≡ w
      → Path G w u
      → Path G v u
```
