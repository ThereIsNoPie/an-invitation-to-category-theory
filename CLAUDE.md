# Project: An Invitation to Category Theory (Literate Agda)

Formalising Fong & Spivak's "An Invitation to Applied Category Theory" in Literate Agda.

**Purpose:** This is a learning tool. The user is working through the textbook, manually reviewing all content to learn category theory. Claude provides insights, corrects misunderstandings, and helps formalise specific items. Do not rush ahead — follow the user's pace and focus on understanding.

## Progress

Tracked in `scripts/translate-to-agda-instructions.md` (`Last Learnt/reviewed` field).

## Agda Development Rules

- **Always type-check** after editing: `agda src/path/to/File.lagda.md`
- **Check plumbing first** before postulating anything — see `src/plumbing/`
- **Check existing definitions** in `src/definitions/` before creating new types
- **Prefer local definitions over stdlib** (e.g. use `definitions.chapter1.Preorder`, not `Relation.Binary`)
- **No universe polymorphism** — use `Set` and `Set₁` only
- **Simple over clever** — explicit case splits over abstract proofs
- **Postulates OK** for reals, classical logic, etc. (via plumbing)
- **Comments only where non-obvious**
- **Minimal imports** — only import what you use

## Module Naming

`<type>.chapter<N>.<PascalCaseName>` — e.g. `definitions.chapter2.VCategory`

| Type | Folder |
|------|--------|
| Definition | `src/definitions/chapterN/` |
| Example | `src/examples/chapterN/` |
| Exercise | `src/exercises/chapterN/` |
| Proposition/Theorem | `src/propositions/chapterN/` |

## Finding Textbook Items

**Primary:** Search `fong_spivak_source/copy-paste-pdf/chapterN.txt`:
```bash
grep "Definition 2.XX\|Example 2.XX\|Exercise 2.XX" fong_spivak_source/copy-paste-pdf/chapter2.txt
```

**Fallback:** Count from LaTeX source — each `\begin{definition}`, `\begin{example}`, `\begin{exercise}`, `\begin{theorem}`, `\begin{proposition}`, `\begin{construction}` increments by 1. `\begin{remark}` is NOT numbered but `\begin{construction}` IS.

## Import Patterns

```agda
-- Local definitions (preferred)
open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder using (SymmetricMonoidalPreorder)

-- Stdlib (when no local equivalent)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
```

## Opening Modules — Common Patterns

```agda
-- Pattern 1: Alias then open fields (aliases MUST come before opens in where blocks)
module X = VCategory X
module Y = VCategory Y
open SymmetricMonoidalPreorder V

-- Pattern 2: Rename to avoid conflicts
open Preorder P renaming (_≤_ to _≤P_)
open Preorder Q renaming (_≤_ to _≤Q_)

-- Pattern 3: Re-export from bundled record
open IsPreorder isPreorder public
```

## Equational Reasoning

Use `plumbing.EquationalReasoning`. The **most common pattern** is mixed preorder + equality:

```agda
open import plumbing.EquationalReasoning using (module ≤-≡-Reasoning)
open ≤-≡-Reasoning _≤_ reflexive transitive

proof : x ≤ z
proof =
  begin
    x
  ≡˘⟨ left-unit ⟩    -- equality backward
    I ⊗ x
  ≤⟨ mono p q ⟩       -- preorder step
    y ⊗ y'
  ≡⟨ assoc ⟩          -- equality forward
    z
  ∎
```

Other modules: `≡-Reasoning` (pure equality), `≤-Reasoning` (pure preorder).

## Code Structure: Signatures vs Implementations

All files should separate **type signatures** (the high-level concept) from **implementations** (the low-level details). Type signatures represent what the textbook is expressing; implementations are the proof/construction details. A human reader should be able to read only the signatures and understand the concept, then expand into details later if they choose.

For **exercises**, this means a `## Problem` section (signatures) and `## Solution` section (implementations). For **definitions/examples/propositions**, use the same principle — present the record type or key signatures first, then the construction.

Since the file is literate Agda, placing a type signature in one code block and the implementation in a later code block compiles naturally — no postulates or holes needed.

**Section names control rendering.** Always start from `scripts/template.lagda.md`. The HTML layout collapses sections with these exact headings, so the reader lands directly on the Problem statement: `Textbook Exercise`/`Textbook Definition`/`Textbook Description`/`Textbook Statement`, `Agda Setup`/`Setup`, `Solution`, `Proof`, `Implementation`, `Construction` (the last four also with `: ...` suffixes). Standard order:

1. `## Textbook Exercise` (collapsed) — verbatim textbook quote
2. `## Agda Setup` (collapsed) — module header + imports only
3. optional visible context sections
4. `## Problem` (visible) — the first Agda the reader sees: signatures that map directly onto the textbook sentence
5. `## Solution` (collapsed) — implementations
6. optional visible `## Interpretation` etc.

See `exercises/chapter2/OppositeDaggerSkeletal.lagda.md` (2.52) or `exercises/chapter2/ClosureIsAdjunction.lagda.md` (2.59) for reference.

## LaTeX Rendering Pitfalls

kramdown parses markdown before MathJax, so:
- `|` for absolute value → use `\lvert x \rvert` not `|x|` (pipes become table delimiters)
- `_` for subscripts in prose → escape as `\_` outside math mode
- `*` for multiplication in prose → escape as `\*` outside math mode
- `<` and `>` → use `\lt` and `\gt` if causing HTML issues
- **Avoid** `\begin{aligned}`, `\begin{gather}`, `\begin{array}` — often unsupported
- For multi-step derivations, use multiple separate `$$...$$` blocks or prose with inline math

## When to Skip

Skip items that are:
- Pure prose/motivation with nothing to formalise
- Require heavy real number machinery with no payoff
- Already covered by a previous formalisation

Ask the user if unsure.

## Plumbing Available

- **`plumbing.Reals`**:
  - `ℝ` with `_≤ℝ_`, `_≥ℝ_`, `_+_`, `_-_`, `_*_`, `-_`, `∣_∣`
  - `[0,∞]` with `0∞`, `∞`, `_≥_`, `_+ℝ_` (extended nonnegative reals for Cost)
  - `dist` : ℝ → ℝ → [0,∞] with `dist-refl`, `dist-sym`, `dist-triangle`
- **`plumbing.ClassicalPostulates`**: `funext`, `propext`, `proof-irrelevance`, `LEM`, quotients (`_/_`, `[_]`)
- **`plumbing.EquationalReasoning`**: `≡-Reasoning`, `≤-Reasoning`, `≤-≡-Reasoning`

## Available Definitions (prefer over stdlib)

Chapter 1: `Preorder`, `IsPreorder`, `MonotoneMap`, `GaloisConnection`, `MeetJoin`, `ClosureOperator`, `EquivalenceRelation`, `Partition`, `Quotient`

Chapter 2: `SymmetricMonoidalPreorder`, `SymmetricMonoidalStructure`, `MonoidalMonotone`, `VCategory`, `VFunctor`, `IsVFunctor`, `VProduct` (`_×V_`), `MetricSpace`, `ExtendedMetricSpace`, `LawvereMetricSpace`, `MonoidalClosed`, `IsMonoidalClosed`, `MonoidalClosedPreorder`, `Quantale`, `HasAllJoins`

Examples: `Cost` (uses `plumbing.Reals` for `[0,∞]`)
