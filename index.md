---
layout: default
title: Home
---

<div class="hero" markdown="1">

# An Invitation to Category Theory

Formalized in Agda with clickable, interactive code

</div>

<div class="section" markdown="1">

## Introduction

_This section will be filled in later with a short summary of what this project is about and a brief explanation of how Agda works._

### About This Project

This is a formalization of category-theoretic concepts in Agda. The code features:

- Fully type-checked proofs in Agda
- Clickable identifiers that link to their definitions
- Syntax highlighting for better readability
- Interactive exploration of mathematical structures

### How Agda Works

_Coming soon: A brief introduction to dependent types, pattern matching, and proof construction in Agda._

</div>

<div class="section" markdown="1">

## Contents

### Core Constructs

1. [Preorder](docs/core-constructs.Preorder.html) - Basic definitions of preorders, monotonic functions, and Galois connections
2. [GraphViz](docs/core-constructs.GraphViz.html) - Utilities for visualizing preorders and graphs

### Exercises

1. [Galois Theorems](docs/exercises.GaloisTheorems.html)
   - 1.1 Proposition 1.101: Equivalence between Galois connections and unit/counit conditions
   - 1.2 Proposition 1.104: Right adjoints preserve meets, left adjoints preserve joins
   - 1.3 Theorem 1.108: Adjoint Functor Theorem for Preorders

### Examples

1. [Apples and Buckets](docs/examples.ApplesAndBuckets.html) - Example 1.109: Three adjoint functors induced by a function
2. [Simple Preorder](docs/examples.SimplePreorder.html) - A concrete diamond-shaped preorder with 4 elements
3. [Meet Example](docs/examples.MeetExample.html) - Demonstrations of meet and join operations
4. [Visualize Diamond](docs/examples.VisualizeDiamond.html) - Executable GraphViz visualization

</div>

<div class="section" markdown="1">

## Navigation Tips

- Click on any identifier in the Agda code to jump to its definition
- Use your browser's back button to return to where you were
- Start with [Everything.agda](docs/Everything.html) to see all module imports

</div>

<footer markdown="1">

Generated with [Agda](https://github.com/agda/agda) • Formalization based on _An Invitation to Applied Category Theory_

[View on GitHub](https://github.com/yourusername/an-invitation-to-category-theory)

</footer>
