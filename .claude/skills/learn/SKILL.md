Work through the next textbook item with the user, one item at a time, for the purpose of **learning category theory**.

This is not a content-production tool. The goal is the human's understanding. The Agda formalisation serves that goal — it is not the goal itself.

## Step 1: Find the next item

Check `scripts/translate-to-agda-instructions.md` for `Last Learnt/reviewed`. Find the next item in the textbook:

```
grep "Definition 2.XX\|Example 2.XX\|Exercise 2.XX\|Proposition 2.XX\|Construction 2.XX\|Remark 2.XX" fong_spivak_source/copy-paste-pdf/chapter2.txt
```

**Important:** Include ALL items in the sequence — numbered items (Definition, Example, Exercise, Proposition, Construction) AND unnumbered Remarks. The human needs to understand the full narrative, not just the formalisable parts.

If the number isn't found, use the fallback: count from LaTeX source. `\begin{remark}` is NOT numbered but `\begin{construction}` IS.

## Step 2: Read the textbook text

Read the full item from the copy-paste PDF. Also read surrounding context (a few lines before/after) to understand where it fits in the narrative.

## Step 3: Check if a file already exists

Search for an existing `.lagda.md` file with the matching number:
```
grep -r "number: XX" src/ --include="*.lagda.md" -l
```

This determines the path: **review & improve** an existing file, or **create a new one**, or **explain without formalising**.

## Step 4: Present the item to the human

**Always** start by explaining the item conversationally to the human. This is the learning step. Include:

- **What it says** — paraphrase in plain language, not just the textbook quote
- **Why it matters** — where does this fit in the chapter's arc? What does it unlock?
- **Key intuition** — diagrams, concrete examples, analogies. Draw things out:
  - Preorders/categories → Hasse diagrams
  - Matrices → write out the matrix
  - Functions → input/output examples
  - Proofs → outline the logical steps before diving in
  - New concepts → connect to something already known
- **Gotchas** — common misunderstandings or subtle points

For **Remarks and pure prose**: explain the content, note what it connects to, and update `Last Learnt/reviewed`. No formalisation needed — but the human still needs to understand it.

For **Exercises**: do NOT show the solution immediately. Present the problem, give hints if needed, and ask if the human wants to attempt it or see the solution.

## Step 5: Handle the formalisation

### If a file already exists:
1. Read it carefully
2. Evaluate its quality as a **learning document**:
   - Does the prose explain the concept clearly, or just restate the textbook?
   - Are there diagrams/examples that build intuition?
   - Is the Problem/Solution or Definition/Construction split clean?
   - Are comments helpful or just noise?
   - Does the interpretation section (if any) add value?
3. Suggest specific improvements, or make them if they're clearly better
4. If the human has stated formatting preferences (in this conversation or in CLAUDE.md), apply them
5. Run `agda` to verify after any changes

### If no file exists and the item is worth formalising:
1. Use the `/next-item` workflow (steps 4-6 from that skill) to create the file
2. But do it **one item only** — do not batch
3. Focus on making the document a good learning resource, not just correct Agda

### If the item should not be formalised:
- Remarks, pure prose, motivation sections — just explain them
- Items requiring heavy machinery with no learning payoff — explain what they say and why we skip
- Still update progress

## Step 6: Check HTML rendering

After any file creation or modification, check for rendering bugs:

1. **Build**: Run `scripts/build-local.sh` to regenerate the HTML site.
2. **Read the output HTML**: Read `_site/docs/<module-path>.html` (e.g. `_site/docs/definitions.chapter2.MonoidalClosed.html`) and check the `<main class="main-content">` section for rendering bugs.
3. **Known rendering bugs to check for**:
   - **Bare code blocks parsed as Agda**: ` ``` ` without a language tag in `.lagda.md` gets parsed as Agda code. **Fix**: use ` ```text ` for ASCII diagrams.
   - **Broken LaTeX from kramdown**: `|` becomes table delimiters (use `\lvert`/`\rvert`), `_` and `*` in prose trigger emphasis (escape as `\_`, `\*`), unsupported environments (`\begin{aligned}` etc.).
   - **`<` and `>` in math**: Can be parsed as HTML tags. Use `\lt` and `\gt`.
4. **Fix issues** in the source `.lagda.md`, re-run `agda`, then `scripts/build-local.sh` again.

## Step 7: Update progress

Update `Last Learnt/reviewed` in `scripts/translate-to-agda-instructions.md`.

## Step 8: Check in with the human

After completing one item, ask:

> Ready for the next item, or do you have questions about this one?

If the human has questions, answer them. If they want to discuss the concept further, discuss it. If they want to modify the document, modify it. The pace is the human's.

## Principles

- **One item at a time.** Never batch. Never rush ahead.
- **Explain before formalising.** The prose comes first, the Agda serves it.
- **Every item matters.** Remarks and prose are part of the narrative. Don't skip them silently.
- **The document is for reading.** When reviewing or creating files, optimise for a human reading the rendered HTML or scrolling in an editor — not for Agda elegance.
- **Respect the human's pace and preferences.** If they say "I already understand this, skip ahead" — skip. If they want to linger — linger. If they want documents formatted a certain way — remember and apply it.