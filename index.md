---
layout: default
title: Home
---

<div class="hero" markdown="1">

# An Invitation to Category Theory

Formalized in Agda with clickable, interactive code

</div>

<div class="section" markdown="1">

## About

This is a formalization of category-theoretic concepts in Agda, focusing on preorders, Galois connections, and adjoint functors. The code features:

- Fully type-checked proofs in Agda
- Clickable identifiers that link to their definitions
- Syntax highlighting for better readability
- Interactive exploration of mathematical structures

</div>

<div class="section" markdown="1">

## Core Theory

<div class="module-grid" markdown="1">

<div class="module-card" markdown="1">

<span class="badge badge-core">Core</span>

### Preorder

Defines preorders, monotonic functions, Galois connections, and proves key theorems including the Adjoint Functor Theorem for preorders (Theorem 1.108).

[View module →](docs/Preorder.html)

</div>

<div class="module-card" markdown="1">

<span class="badge badge-core">Core</span>

### GraphViz

Utilities for visualizing preorders and graphs using GraphViz DOT format. Includes text and DOT output generation.

[View module →](docs/GraphViz.html)

</div>

<div class="module-card" markdown="1">

<span class="badge badge-core">Core</span>

### MeetExample

Demonstrates meet and join operations in preorders with concrete examples of lattice structures and their properties.

[View module →](docs/MeetExample.html)

</div>

</div>

</div>

<div class="section" markdown="1">

## Examples

<div class="module-grid" markdown="1">

<div class="module-card" markdown="1">

<span class="badge badge-example">Example</span>

### Apples and Buckets

Example 1.109: Demonstrates three adjoint functors induced by a function, using the intuitive metaphor of apples and buckets.

[View module →](docs/examples.ApplesAndBuckets.html)

</div>

<div class="module-card" markdown="1">

<span class="badge badge-example">Example</span>

### Simple Preorder

A concrete example of a diamond-shaped preorder with 4 elements, showing how to construct preorders from directed graphs.

[View module →](docs/examples.SimplePreorder.html)

</div>

<div class="module-card" markdown="1">

<span class="badge badge-example">Example</span>

### Visualize Diamond

Executable module that generates GraphViz visualizations of the diamond preorder, demonstrating the integration of proof and visualization.

[View module →](docs/examples.VisualizeDiamond.html)

</div>

</div>

</div>

<div class="section" markdown="1">

## Key Theorems

- **Proposition 1.101**: Equivalence between Galois connections and unit/counit conditions [(Preorder.agda)](docs/Preorder.html#FromGalois)
- **Proposition 1.104**: Right adjoints preserve meets, left adjoints preserve joins [(Preorder.agda)](docs/Preorder.html#Prop104)
- **Theorem 1.108**: Adjoint Functor Theorem for Preorders - a monotonic function is an adjoint iff it preserves the appropriate limits [(Preorder.agda)](docs/Preorder.html#Theorem108)
- **Example 1.109**: Apples and Buckets - three adjoint functors induced by a function [(ApplesAndBuckets.agda)](docs/examples.ApplesAndBuckets.html)

<div class="code-example" markdown="1">

### Example: Adjunction with Clickable Code

The first adjunction `f! ⊣ f*` says that for all subsets A' ⊆ A and B' ⊆ B, we have f!(A') ⊆ B' if and only if A' ⊆ f*(B'). Here's the type signature (click on identifiers to jump to their definitions):

```agda
f!⊆→⊆f* : ∀ {A' B'} → f! A' ⊆ B' → A' ⊆ f* B'
```

<p class="code-caption">
<em>Try clicking on <code>f!</code>, <code>f*</code>, or <code>⊆</code> to navigate to their definitions!</em>
</p>

</div>

</div>

<div class="section" markdown="1">

## Navigation

Click on any identifier in the Agda code to jump to its definition. Use your browser's back button to return to where you were.

Start with [`Everything.agda`](docs/Everything.html) to see all imports, or dive directly into [`Preorder.agda`](docs/Preorder.html) for the core theory.

</div>

<footer markdown="1">

Generated with [Agda](https://github.com/agda/agda) • Formalization based on _An Invitation to Applied Category Theory_

[View on GitHub](https://github.com/yourusername/an-invitation-to-category-theory)

</footer>
