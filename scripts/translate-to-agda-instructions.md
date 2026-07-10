# Translating Fong & Spivak to Agda

## Goal

Create clean, minimal Agda that's easy to understand and learn from.

## Current Progress

- **Last Learnt/reviewed** 2.64


## Step 1: Find the Next Item

**Primary Method (recommended):** Use the copy-paste PDF files in `fong_spivak_source/copy-paste-pdf/`:

1. Check the last completed `.lagda.md` file's YAML frontmatter for `number:`
2. Search the copy-paste file for that number: `grep "Definition 2.XX\|Example 2.XX" fong_spivak_source/copy-paste-pdf/chapter2.txt`
3. The PDF copy-paste has explicit numbering like "Definition 2.48", "Example 2.49", etc.
4. This is the most reliable method since numbers are explicit in the text

**Fallback Method:** Count from the LaTeX source:

1. Search for the item's unique text in the LaTeX source
2. Read the LaTeX from that line onwards
3. Count: each `\begin{definition}`, `\begin{example}`, `\begin{exercise}`, `\begin{theorem}`, `\begin{proposition}`, or `\begin{construction}` increments the number by 1

**Note:** `\begin{remark}` is NOT a numbered item, but `\begin{construction}` IS numbered.

## Step 2: Read and Understand

Read the LaTeX source. Before writing any Agda, **draw out the structure as text**:

- For preorders/categories: draw the Hasse diagram
- For matrices: write out the matrix
- For functions: show input → output examples
- For proofs: outline the logical steps

Example - before coding Example 2.31, first draw:
```
Hasse diagram:
p → q
↓   ↓
r → s
    ↓
    t

Matrix X(row, col) where ⊤ = true, ⊥ = false:
    p q r s t
p   ⊤ ⊤ ⊤ ⊤ ⊤
q   ⊥ ⊤ ⊥ ⊤ ⊤
r   ⊥ ⊥ ⊤ ⊤ ⊤
s   ⊥ ⊥ ⊥ ⊤ ⊤
t   ⊥ ⊥ ⊥ ⊥ ⊤
```

This makes the Agda obvious to write.

## Step 3: Write Minimal Agda

Use `scripts/template.lagda.md` as base. Key structure:

```markdown
---
layout: agda
title: "Title"
section: "Definitions"  # or Examples, Exercises, Propositions
chapter: 2
number: N
---

# Title

## Textbook Exercise

(Section names matter: the HTML layout collapses `Textbook Exercise`/`Textbook
Definition`/`Textbook Description`/`Textbook Statement`, `Agda Setup`/`Setup`,
`Solution`, `Proof`, `Implementation`, `Construction` — so the reader lands on
the visible `## Problem` section. See `scripts/template.lagda.md`.)

Quote textbook. Use LaTeX for math: $d(x,y)$ inline, $$d(x,y) \geq 0$$ display.

**LaTeX rendering pitfalls** (kramdown parses markdown before MathJax):
- `|` for absolute value → use `\lvert x \rvert` not `|x|` (pipes become table delimiters)
- `_` for subscripts in prose → escape as `\_` outside math mode
- `*` for multiplication in prose → escape as `\*` outside math mode
- `<` and `>` → use `\lt` and `\gt` if causing HTML issues

**Display equations:**
- Single-line: `$$I_W \leq f(I_V) \leq f(C(c,c))$$`
- **Avoid** `\begin{aligned}`, `\begin{gather}`, `\begin{array}` — often unsupported
- For multi-step derivations, use a single long line or multiple separate `$$...$$` blocks
- If a derivation is complex, prefer prose with inline math over display blocks

## Agda Setup

\```agda
module TYPE.chapterN.Name where
-- imports only — this section is collapsed in the rendered HTML
\```

## Problem

Diagrams (use \```svg fences — see the Diagrams section below), matrices,
tables to clarify structure. ASCII in \```text fences is fine as a fallback.

The first Agda the reader sees: type signatures that map directly onto the
textbook statement.

\```agda
-- statement : Hypothesis → Conclusion
\```

## Solution

\```agda
-- statement = ... (implementations/proofs, collapsed in the rendered HTML)
\```
```

Guidelines:
- **Minimal imports** - check `src/definitions/` first, prefer local over stdlib
- **No levels** - use `Set`, `Set₁`
- **Postulates OK** for reals, etc.
- **Simple over clever** - explicit case splits over abstract proofs
- **Comments only where non-obvious**
- **Exercises: split into Problem and Solution** - Put type signatures (and any necessary definitions/records) in a `## Problem` section, and implementations/proofs in a `## Solution` section. This lets readers attempt the exercise before seeing the answer. See `exercises/chapter2/OppositeDaggerSkeletal.lagda.md` or `exercises/chapter2/ClosureIsAdjunction.lagda.md` for good examples.

## Diagrams (SVG)

**When to add:** diagrams are opt-in. By default pages have no diagrams — add
one only when the user asks (typically because they're confused) or when the
item is clearly hard to follow without one. Don't decorate.

Rendered diagrams go in ` ```svg ` fenced blocks containing hand-written inline
SVG. The layout unwraps these client-side into live SVG. Never write raw
`<svg>` HTML outside a fence — kramdown mangles it.

Conventions:
- **`viewBox` only, no `width`/`height` attributes** — CSS scales the diagram.
  Leave ~20 units of padding around content so strokes/labels aren't clipped.
- **Theme-aware colors**: `stroke="currentColor"` and `fill="currentColor"`
  everywhere; the layout sets the diagram's color to the page text color in
  both light and dark mode. For accents use CSS variables sparingly, e.g.
  `stroke="var(--agda-function)"`.
- **Text**: `font-size="16"`, `text-anchor="middle"`, no `font-family` (inherits
  the page font). Unicode math in labels is fine: ≤ ⊗ ∘ ∞ ⊤ ⊥ subscripts.
- **Arrowheads**: the layout defines shared markers — use
  `marker-end="url(#arrow)"` (solid) or `marker-end="url(#arrow-open)"` (open).
  End arrow lines a few units short of the target node so the head isn't
  swallowed. A self-contained `<defs>` inside the diagram also works if needed.
- **Commutative squares with real math labels**: prefer MathJax `amscd` over
  SVG — `$$\begin{CD} A @>f>> B \\ @VgVV @VVhV \\ C @>k>> D \end{CD}$$`.
  (Grid-only: no diagonal arrows; for diagonals use SVG.)
- **Wiring diagrams / quick sketches**: ASCII in ` ```text ` fences is still fine.

Example — Hasse diagram of a preorder (a, b below c, c below d):

```svg
<svg viewBox="0 0 200 240" role="img" aria-label="Hasse diagram">
  <text x="60" y="206" font-size="16" text-anchor="middle" fill="currentColor">a</text>
  <text x="140" y="206" font-size="16" text-anchor="middle" fill="currentColor">b</text>
  <text x="100" y="126" font-size="16" text-anchor="middle" fill="currentColor">c</text>
  <text x="100" y="46" font-size="16" text-anchor="middle" fill="currentColor">d</text>
  <line x1="66" y1="186" x2="92" y2="140" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="134" y1="186" x2="108" y2="140" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="100" y1="106" x2="100" y2="60" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
</svg>
```

For weighted graphs (Cost), label edges with `<text>` beside the line, e.g.
distance values; curve parallel/opposite edges with
`<path d="M ... Q ... ..." fill="none">`.

## Step 4: Compile and Add

```bash
agda src/path/to/File.lagda.md
```

Add import to `src/Everything.agda` in the correct section.

## Step 5: Summarize

After 2 files that compile:
1. Brief summary of what each formalizes
2. "Ready to continue?"

## File Locations

| Type | Folder |
|------|--------|
| Definition | `src/definitions/chapter2/` |
| Example | `src/examples/chapter2/` |
| Exercise | `src/exercises/chapter2/` |
| Proposition/Theorem | `src/propositions/chapter2/` |

## When to Skip

Skip items that are:
- Pure prose/motivation
- Require heavy real number machinery with no payoff
- Repeated from earlier (already formalized)

Ask the user if unsure.

## Plumbing (check first!)

`src/plumbing/` has common postulates - **use these instead of re-postulating**:

- **`Reals`** - real numbers (general, then metric-specific):
  - `ℝ` with ordering (`_≤ℝ_`, `_≥ℝ_`), arithmetic (`_+_`, `_-_`, `_*_`, `-_`), absolute value (`∣_∣`)
  - `[0,∞]` with `0∞`, `∞`, `_≥_`, `_+ℝ_` (extended nonnegative reals for Cost)
  - `dist` : ℝ → ℝ → [0,∞] with `dist-refl`, `dist-sym`, `dist-triangle` (metric space distance)

- **`ClassicalPostulates`** - classical logic:
  - `funext`, `propext`, `proof-irrelevance`
  - `LEM` (law of excluded middle)
  - Quotient types `_/_`, `[_]`

- **`EquationalReasoning`** - proof combinators

## Available Definitions (prefer these over stdlib)

Chapter 1:
- `Preorder`, `IsPreorder`
- `MonotoneMap`
- `GaloisConnection`
- `MeetJoin`
- `ClosureOperator`
- `EquivalenceRelation`
- `Partition`, `Quotient`

Chapter 2:
- `SymmetricMonoidalPreorder`, `SymmetricMonoidalStructure`
- `MonoidalMonotone`
- `VCategory`
- `VFunctor`, `IsVFunctor`
- `VProduct` (`_×V_`)
- `MetricSpace`, `ExtendedMetricSpace`
- `LawvereMetricSpace`
- `MonoidalClosed`, `IsMonoidalClosed`, `MonoidalClosedPreorder`
- `Quantale`, `HasAllJoins`

Examples:
- `Cost` - uses `plumbing.Reals` for `[0,∞]`

## Template

Use `scripts/template.lagda.md` - it's minimal and has the right structure.
