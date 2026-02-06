# Translating Fong & Spivak to Agda

## Goal

Create clean, minimal Agda that's easy to understand and learn from.

## Current Progress

- **Last Learnt/reviewed** 2.56


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

## Textbook

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

## Diagram

ASCII diagrams, matrices, tables to clarify structure.

## Agda

\```agda
module TYPE.chapterN.Name where
-- code
\```
```

Guidelines:
- **Minimal imports** - check `src/definitions/` first, prefer local over stdlib
- **No levels** - use `Set`, `Set₁`
- **Postulates OK** for reals, etc.
- **Simple over clever** - explicit case splits over abstract proofs
- **Comments only where non-obvious**
- **Exercises: split into Problem and Solution** - Put type signatures (and any necessary definitions/records) in a `## Problem` section, and implementations/proofs in a `## Solution` section. This lets readers attempt the exercise before seeing the answer. See `exercises/chapter2/PowerSetIntersection.lagda.md` for a good example.

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
