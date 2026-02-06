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

4. **Write the Agda**: Use `scripts/template.lagda.md` as base. Check `src/plumbing/` and `src/definitions/` before creating new types or postulating.

   **Always** split the code into two sections:
   - **First code block**: Type signatures, record definitions, and any supporting types — this is the high-level concept from the textbook. A reader should understand what's going on from this alone.
   - **Second code block** (after a `## Solution` or `## Construction` heading): Implementations and proofs — the low-level details a reader can look into later.

   For exercises, label these `## Problem` and `## Solution`. For definitions/examples/propositions, use `## Definition` / `## Construction` or similar. No postulates or holes needed — literate Agda compiles type signatures and implementations across separate code blocks.

5. **Compile**: Run `agda src/path/to/File.lagda.md`. Fix any errors.

6. **Register**: Add import to `src/Everything.agda` in the correct section.

7. **Update progress**: Update `Last Learnt/reviewed` in `scripts/translate-to-agda-instructions.md`.

8. **Summarise**: After 2 completed files, give a brief summary of what each formalises, then ask "Ready to continue?"
