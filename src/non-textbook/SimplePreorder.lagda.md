---
layout: agda
title: "Simple Preorder"
section: "Not In Textbook"
chapter: 1
number: 3
---

```agda
module non-textbook.SimplePreorder where

open import definitions.Preorder
open import non-textbook.GraphViz
open import Data.String using (String)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

-- A simple finite preorder with 4 elements arranged in a diamond:
--
--       Top
--      /   \
--   Left   Right
--      \   /
--      Bottom
--
-- The ordering relation ≤ represents:
--   Bottom ≤ Left ≤ Top
--   Bottom ≤ Right ≤ Top
-- Plus reflexivity and transitivity

-- Reflexive-transitive closure of a relation
data RTClosure {A : Set} (R : A → A → Set) : A → A → Set where
  rt-refl  : ∀ {x} → RTClosure R x x
  rt-step  : ∀ {x y} → R x y → RTClosure R x y
  rt-trans : ∀ {x y z} → RTClosure R x y → RTClosure R y z → RTClosure R x z

-- Convert a graph to a preorder by taking the reflexive-transitive closure
graphToPreorder : Graph → Preorder
graphToPreorder G = record
  { Carrier = Vertex
  ; _≤_ = RTClosure Edge
  ; isPreorder = record
      { reflexive = λ {x} → rt-refl
      ; transitive = λ {x} {y} {z} → rt-trans
      }
  }
  where open Graph G

-- Four elements for our diamond example
data FourElements : Set where
  Bottom : FourElements
  Left   : FourElements
  Right  : FourElements
  Top    : FourElements

-- Define only the base edges (no reflexivity or transitivity needed!)
data DiamondEdge : FourElements → FourElements → Set where
  bottom-left  : DiamondEdge Bottom Left
  bottom-right : DiamondEdge Bottom Right
  left-top     : DiamondEdge Left Top
  right-top    : DiamondEdge Right Top

-- The diamond graph
DiamondGraph : Graph
DiamondGraph = record
  { Vertex = FourElements
  ; Edge = DiamondEdge
  }

-- The preorder generated from the graph
DiamondPreorder : Preorder
DiamondPreorder = graphToPreorder DiamondGraph

-- Convenient alias for the ordering relation
_≤_ : FourElements → FourElements → Set
_≤_ = RTClosure DiamondEdge

-- Example: proving Bottom ≤ Top using the graph edges
example : Bottom ≤ Top
example = rt-trans (rt-step bottom-left) (rt-step left-top)

-- Alternative proof using transitivity explicitly
example' : Bottom ≤ Top
example' = Preorder.transitive DiamondPreorder (rt-step bottom-left) (rt-step left-top)

-- Visualization configuration for the diamond graph
showFourElements : FourElements → String
showFourElements Bottom = "Bottom"
showFourElements Left   = "Left"
showFourElements Right  = "Right"
showFourElements Top    = "Top"

diamondVertices : List FourElements
diamondVertices = Bottom ∷ Left ∷ Right ∷ Top ∷ []

-- Note: We cannot pattern match on DiamondEdge constructors directly,
-- so we enumerate the edges explicitly
diamondEdges : List (FourElements × FourElements)
diamondEdges = (Bottom , Left) ∷ (Bottom , Right) ∷ (Left , Top) ∷ (Right , Top) ∷ []

diamondGraphVizConfig : GraphVizConfig FourElements
diamondGraphVizConfig = record
  { showVertex = showFourElements
  ; vertices = diamondVertices
  ; edges = diamondEdges
  }

-- Generate DOT format visualization
-- Copy the output and paste into https://dreampuf.github.io/GraphvizOnline/
diamondDot : String
diamondDot = graphToDot diamondGraphVizConfig

-- Generate text representation
diamondText : String
diamondText = graphToText diamondGraphVizConfig
```
