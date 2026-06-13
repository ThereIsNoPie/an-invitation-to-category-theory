Formalise the next textbook item from Fong & Spivak into Literate Agda.

## Steps

1. **Find the next item**: Check `scripts/translate-to-agda-instructions.md` for `Last Learnt/reviewed`. Search the copy-paste PDF for the next numbered item:
   ```
   grep "Definition 2.XX\|Example 2.XX\|Exercise 2.XX\|Proposition 2.XX\|Construction 2.XX" fong_spivak_source/copy-paste-pdf/chapter2.txt
   ```
   If the number isn't found, use the fallback: count `\begin{definition}`, `\begin{example}`, `\begin{exercise}`, `\begin{theorem}`, `\begin{proposition}`, `\begin{construction}` from the LaTeX source. `\begin{remark}` is NOT numbered but `\begin{construction}` IS.

2. **Read and understand**: Read the textbook text. Before writing any Agda, draw out the structure:
   - Preorders/categories: Hasse diagram
   - Matrices: write out the matrix
   - Functions: show input → output examples
   - Proofs: outline the logical steps

3. **Evaluate**: Decide if it's worth formalising (in the context of whether formalising it will help the reader learn or whether an informal explanation is just as good/better). Skip items that are pure prose/motivation, require heavy real number machinery with no payoff, or are too heavily reliant on new postulates. If skipping, explain what the item says and why it's a skip, then update `Last Learnt/reviewed` and move to the next item. Ask the user if unsure.

4. **Write the Agda**: Use `scripts/template.lagda.md` as base — its section names are load-bearing. Check `src/plumbing/` and `src/definitions/` before creating new types or postulating.

   **Section names control rendering.** The HTML layout collapses sections named `Textbook Exercise`/`Textbook Definition`/`Textbook Description`/`Textbook Statement`, `Agda Setup`/`Setup`, `Solution`, `Proof`, `Implementation`, `Construction` (the last four also with `: ...` suffixes), so the reader lands directly on the problem statement. Standard order:

   1. `## Textbook Exercise` (or `Textbook Definition`/`Textbook Description`) — verbatim quote, collapsed.
   2. `## Agda Setup` — module header + imports only, collapsed.
   3. Optional visible context sections (supporting types the reader needs).
   4. `## Problem` (visible) — **the first Agda the reader sees must be a concise rendering of the textbook statement**: type signatures that map directly onto the textbook sentence. For definitions/examples/propositions name it after the concept (e.g. `## Definition`, `## Statement`) — just keep it visible.
   5. `## Solution` (collapsed) — implementations and proofs. For definitions/propositions use `## Construction`, `## Implementation` or `## Proof`.
   6. Optional visible `## Interpretation` etc.

   No postulates or holes needed — literate Agda compiles type signatures and implementations across separate code blocks, even with a nested module declared in between.

   **HTML rendering rules:**
   - **Use ` ```text ` not bare ` ``` `** for ASCII diagrams — bare fenced blocks get parsed as Agda in `.lagda.md`.
   - **Escape kramdown-sensitive characters in prose**: `|` → `\lvert`/`\rvert`, `_` → `\_`, `*` → `\*`, `<`/`>` → `\lt`/`\gt`.
   - **Avoid** `\begin{aligned}`, `\begin{gather}`, `\begin{array}` — unsupported by kramdown+MathJax pipeline.

5. **Compile**: Run `agda src/path/to/File.lagda.md`. Fix any errors.

6. **Register**: Add import to `src/Everything.agda` in the correct section.

7. **Update progress**: Update `Last Learnt/reviewed` in `scripts/translate-to-agda-instructions.md`.

8. **Summarise**: After 2 completed files, give a brief summary of what each formalises, then ask "Ready to continue?"
