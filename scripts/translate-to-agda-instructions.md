# Translating Fong & Spivak to Agda

## Goal

Create clean, minimal Agda that's easy to understand and learn from.

## Current Progress

- **Last completed:** Example 2.37 (Reals as Metric Space)
- **Next item:** Exercise 2.38

## Step 1: Find the Next Item

```bash
grep -n '\\begin{definition}\|\\begin{example}\|\\begin{exercise}\|\\begin{theorem}\|\\begin{proposition}' fong_spivak_source/C2-Resource_theory.tex | nl
```

The left number (31, 32, ...) is the textbook number for Chapter 2.

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

Structure:
```markdown
---
layout: agda
title: "Title"
section: "Definitions"  # or Examples, Exercises, Propositions
chapter: 2
number: N
---

# Title

## Textbook

Quote the textbook definition/example/exercise.

## Diagram (if applicable)

Draw any diagrams, matrices, or examples as text.

## Agda

\```agda
module TYPE.chapterN.Name where

-- imports
-- code
\```
```

Guidelines:
- **Minimal imports** - check `src/definitions/` first, prefer local over stdlib
- **No levels** - use `Set`, `Set₁`
- **Postulates OK** for reals, etc.
- **Simple over clever** - explicit case splits over abstract proofs
- **Comments only where non-obvious**

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
- `MetricSpace`, `ExtendedMetricSpace`
- `LawvereMetricSpace`

Examples:
- `Cost` - uses `plumbing.Reals` for `[0,∞]`

## Template

Use `scripts/template.lagda.md` - it's minimal and has the right structure.
