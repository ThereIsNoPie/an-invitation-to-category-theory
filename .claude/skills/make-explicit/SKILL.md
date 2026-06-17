Rewrite a point-free proof term so every intermediate step is spelled out and type-checked, using a combination of equational reasoning and goal-directed reasoning.

The function (and optionally its file) to make explicit is: $ARGUMENTS

## Goal

Take a terse proof like `curry (transitive eval w≤w')` and turn it into a form where a reader can follow the logic top-to-bottom **without entering interactive mode** — every intermediate type or carrier element appears in the source and is verified by Agda. If a stated step is wrong, the file won't compile.

## The two styles (and when each applies)

There are two complementary reasoning vocabularies. The whole skill is choosing, per step, which one fits — and nesting them.

**Equational reasoning** (`≤-Reasoning`, `≤-≡-Reasoning`, `∼-Reasoning`, `≡-Reasoning` in `plumbing.EquationalReasoning`). The lines are **carrier elements** (`a`, `b`, `c`); the relation is fixed and hidden in the `≤⟨ ⟩`/`≡⟨ ⟩` connectives. Use it for a step that **stays within one relation** — a chain of `≤`/`≡`/`∼` between points. This is just composition via `transitive`.

```text
begin  a  ≤⟨ p ⟩  b  ≤⟨ q ⟩  c  ∎      -- proves  a ≤ c
```

**Goal-directed reasoning** (`Goal-Reasoning` in `plumbing.EquationalReasoning`). The lines are **whole statements** (types); each step is an arbitrary function between statements. Use it for a step that **changes the shape of the judgement** — an adjunction transpose (`curry`/`uncurry`), `subst`, or applying a lemma whose conclusion has a different form. Read top-down from the goal:

```text
Goal           by f ⟵      -- to prove Goal, apply f to a proof of the next line
NextStatement  by g ⟵
BaseStatement  witness s   -- base case: s : BaseStatement
```

produces `f (g s)`, with each statement written out and checked.

**The decision rule:** does the step relate two *points* under one relation, or transform the *whole statement*? Points → equational reasoning. Whole statement → goal-directed. A typical proof is a goal-directed outer skeleton (the shape changes) with equational-reasoning chains nested inside the `witness`/`by` steps (the composition runs). Anything expressible in equational reasoning is also expressible goal-directed, but not vice-versa — so reach for equational reasoning whenever a step is a pure relation chain, since it's terser, and fall back to goal-directed for the rest.

## Steps

1. **Locate the function** named in `$ARGUMENTS` (grep `src/` if the file isn't given). Read its type signature and current proof term, and note the local context (what `open`s are in scope, what `reflexive`/`transitive`/lemmas are available).

2. **Decompose the term** inside-out into its steps. For each, determine the type *before* and *after*, and classify it:
   - relation chain between carrier elements → equational reasoning;
   - shape-changing transform of the whole judgement → goal-directed step.

3. **Set up reasoning in scope** (in the relevant `where`/module):
   - `open Goal-Reasoning` — import via `open import plumbing.EquationalReasoning using (module Goal-Reasoning)`. It is relation-agnostic; takes no arguments.
   - For the equational part: if the relation comes from a `Preorder`/`SymmetricMonoidalPreorder`/`MonoidalClosedPreorder`, a `≤-Reasoning` submodule is **already re-exported** — just `open ≤-Reasoning` (no args). **Do not also import `module ≤-Reasoning` from plumbing — that causes an `AmbiguousModule` clash.** Only when no such relation module is in scope, import `module ≤-≡-Reasoning` (or `≤-Reasoning`) from plumbing and apply it: `open ≤-≡-Reasoning _≤_ reflexive transitive`.

4. **Rewrite** the proof: goal-directed skeleton for shape changes, equational `begin … ∎` chains nested inside the relevant `witness`/`by` step. Spell out every intermediate type/element. Keep the original type signature unchanged.

5. **Type-check**: `agda <file>`. Fix any mis-stated intermediate types (the compiler tells you the real one). Re-check any downstream importers if you touched a shared definition.

6. **Report** the before/after and confirm it type-checks.

## Reference example

`src/definitions/chapter2/MonoidalClosed.lagda.md` — `⊸-mono-r` in `module ClosedProperties`. Original:

```agda
⊸-mono-r {v} {w} {w'} w≤w' = curry (transitive eval w≤w')
```

Made explicit — `curry` transposes across the adjunction (goal-directed), and its subgoal is a plain `≤`-chain (equational reasoning) nested inside `witness`:

```agda
⊸-mono-r {v} {w} {w'} w≤w' =
    (v ⊸ w) ≤ (v ⊸ w')   by curry ⟵
    ((v ⊸ w) ⊗ v) ≤ w'    witness
      (begin
        (v ⊸ w) ⊗ v  ≤⟨ eval ⟩
        w            ≤⟨ w≤w' ⟩
        w'           ∎)
```

## Notes

- This is a **learning aid**: prefer it where the user wants to *see* the logic. The terse one-liner is often the better "production" form; mention the tradeoff rather than silently bloating every proof.
- The one bit of irreducible noise is a `λ` when a `by` step's function needs to plumb an extra argument (e.g. `by (λ p → transitive p w≤w')`); that lambda *is* the genuine transformation, so it has to appear.
- Goal-directed lines must state the **full** proposition (both sides of the `≤` and the relation). That verbosity is the point — it's what makes the step checked rather than commented.
