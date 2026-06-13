---
layout: agda
title: "Title Here"
section: "Definitions"
chapter: 2
number: N
---

# Title Here

<!--
SECTION NAMING MATTERS: the HTML layout (_layouts/agda.html) collapses sections
with these exact h2/h3 names, so the reader lands directly on the problem
statement:

  Collapsed by default:  "Textbook Exercise", "Textbook Definition",
                         "Textbook Description", "Agda Setup", "Setup",
                         "Solution"/"Solution: ...", "Proof"/"Proof: ...",
                         "Implementation"/"Implementation: ..."
  Always visible:        everything else — especially "Problem"

Standard order: Textbook quote (collapsed) → Agda Setup (collapsed) →
optional visible context sections → Problem (visible, headline signatures) →
Solution (collapsed, implementations) → optional Interpretation (visible).
-->

## Textbook Exercise

<!-- For definitions use "## Textbook Definition", for examples
     "## Textbook Description". These names collapse in the rendered HTML. -->

**[Definition/Example/Exercise/Proposition] 2.N.** Paste the textbook text here.

Use LaTeX for math: $d(x, y) := \lvert y - x \rvert$ for inline, or display:

$$d(x, y) + d(y, z) \geq d(x, z)$$

## Agda Setup

<!-- Module header and imports only — collapsed in the rendered HTML. -->

```agda
module TYPE.chapter2.Name where

-- Check src/plumbing/ for postulates (reals, classical logic)
-- Check src/definitions/ before using stdlib
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## Problem

<!-- This is the first thing the reader sees. It must contain a concise Agda
     rendering of the textbook statement: type signatures (and any supporting
     types needed to read them) that map directly onto the textbook sentence.
     No implementations here — literate Agda compiles a signature in one block
     and its definition in a later block.

     For definitions/examples/propositions name this section after the concept
     instead (e.g. "## Definition", "## Statement") — just keep it visible. -->

Draw any diagrams, matrices, tables as ASCII (note the `text` language tag —
a bare fence is parsed as Agda):

```text
no → maybe → yes
```

```agda
-- Headline signatures here, e.g.:
-- statement : Hypothesis → Conclusion
```

## Solution

<!-- Collapsed in the rendered HTML. Implementations and proofs of the
     signatures declared above. For definitions/propositions use
     "## Construction", "## Implementation" or "## Proof". -->

```agda
-- statement = ...
```
