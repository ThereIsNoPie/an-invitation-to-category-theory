Add a rendered diagram to an existing `.lagda.md` page to clarify a confusing point.

The argument is a file path or a textbook item number, optionally followed by a note on what is confusing: $ARGUMENTS

## Context

Diagrams are opt-in — the user invokes this skill because a page is hard to follow without one. The goal is one diagram that resolves the specific confusion, not decoration. Full authoring conventions: "Diagrams (SVG)" in `scripts/translate-to-agda-instructions.md`. Worked example in the wild: `src/exercises/chapter2/JoinsInBoolAndCost.lagda.md`.

## Steps

1. **Locate the file**. If given an item number instead of a path: `grep -r "number: XX" src/ --include="*.lagda.md" -l`.

2. **Understand the confusion**. Read the file and the corresponding textbook text (`fong_spivak_source/copy-paste-pdf/chapterN.txt`). If the user didn't say what confused them, infer the hardest point on the page (order reversals, quantifier structure, which map goes where) — and say what you picked and why when reporting.

3. **Choose the medium**:
   - Hasse diagrams, weighted graphs (Cost), maps between preorders, anything spatial → inline SVG in a ` ```svg ` fence.
   - Commutative square with real math labels, no diagonals → MathJax amscd: `$$\begin{CD} A @>f>> B \\ @VgVV @VVhV \\ C @>k>> D \end{CD}$$`.
   - Wiring diagrams → ASCII in a ` ```text ` fence (SVG rarely pays off here).

4. **Draw the SVG** following the conventions:
   - `viewBox` only (no width/height), ~20 units padding so nothing clips.
   - `stroke="currentColor"` / `fill="currentColor"`; accents sparingly via `var(--agda-function)`.
   - Text: `font-size="16"`, `text-anchor="middle"`, no font-family. Unicode math (≤ ⊗ ∘ ∞ ⊤ ⊥) in labels.
   - Arrows: `marker-end="url(#arrow)"` (solid) or `url(#arrow-open)"` (open) — shared markers defined by the layout. Stop lines ~6 units short of node text so heads aren't swallowed.
   - Convention for order structures: arrows point *up the order*; put the bottom element at the bottom even when that's counterintuitive (e.g. ∞ in Cost) — that counterintuitive placement is often exactly the point worth showing.
   - Add `role="img"` and an `aria-label` describing the picture.

5. **Place it** in a *visible* section (usually `## Problem` or a context section), right next to what it clarifies, with a one-or-two-sentence prose lead-in saying what to look at. Don't bury it in a collapsed `Solution` unless it explains the proof specifically.

6. **Verify**:
   - The file still type-checks (the hook runs `agda` on save; the svg fence is ignored by Agda).
   - Run `scripts/build-local.sh`, then check `_site/docs/<module-path>.html` contains the block as `<code class="language-svg">` with the SVG intact (it is unwrapped client-side, so it appears HTML-escaped in the static file — that's correct).
   - Sanity-check coordinates: no overlapping labels, arrows attach near the right nodes, everything inside the viewBox with padding.

7. **Report**: what confusion the diagram targets, what it shows, and where it was placed.
