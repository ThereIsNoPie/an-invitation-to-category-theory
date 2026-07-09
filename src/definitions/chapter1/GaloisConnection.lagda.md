---
layout: agda
title: "Galois Connection"
section: "Definitions"
chapter: 1
number: 90
---

# Galois Connection

**Definition 1.90.** A *Galois connection* between preorders P and Q is a pair of monotone maps f : P → Q and g : Q → P such that

f(p) ≤ q if and only if p ≤ g(q).   (1.6)

We say that f is the *left adjoint* and g is the *right adjoint* of the Galois connection.

```agda
module definitions.chapter1.GaloisConnection where

open import definitions.chapter1.Preorder using (Preorder)
open import definitions.chapter1.MonotoneMap using (Monotonic)

-- Galois connection between preorders
record GaloisConnection (P Q : Preorder) : Set where
  open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)

  field
    f : A → B  -- Lower adjoint (left adjoint)
    g : B → A  -- Upper adjoint (right adjoint)

    -- Adjunction property: f(x) ≤₂ y  ⟺  x ≤₁ g(y)
    f-g : ∀ {x y} → f x ≤₂ y → x ≤₁ g y
    g-f : ∀ {x y} → x ≤₁ g y → f x ≤₂ y

  -- Derived properties
  f-monotonic : Monotonic _≤₁_ _≤₂_ f
  f-monotonic x≤y = g-f (Preorder.transitive P x≤y (f-g (Preorder.reflexive Q)))

  g-monotonic : Monotonic _≤₂_ _≤₁_ g
  g-monotonic y≤z = f-g (Preorder.transitive Q (g-f (Preorder.reflexive P)) y≤z)
```

## Two simplest examples: how each adjoint is selected

Rearranging $f(p) \leq q \iff p \leq g(q)$ pins each adjoint down uniquely
(when it exists):

- the **left** adjoint takes the **least** solution: $f(p)$ = the least $q$ with $p \leq g(q)$ — the best approximation of $p$ *from above* in Q;
- the **right** adjoint takes the **greatest** solution: $g(q)$ = the greatest $p$ with $f(p) \leq q$ — the best approximation of $q$ *from below* in P.

### Ceiling and floor

The book's first example: $(3\times -) : \mathbb{Z} \to \mathbb{R}$. Its left
adjoint is $\lceil -/3 \rceil$ (least integer solution) and its right adjoint is
$\lfloor -/3 \rfloor$ (greatest integer solution) — two Galois connections
sharing the middle map. Take $x = 5$: the candidates are the multiples of 3.
The least multiple $\geq 5$ is $6$, so $\lceil 5/3 \rceil = 2$; the greatest
multiple $\leq 5$ is $3$, so $\lfloor 5/3 \rfloor = 1$.

```svg
<svg viewBox="0 0 520 180" role="img" aria-label="Number line of the reals with multiples of 3 marked; x equals 5 sits between 3 and 6; the ceiling adjoint selects the least multiple above x, the floor adjoint the greatest multiple below x">
  <text x="150" y="42" font-size="14" text-anchor="middle" fill="var(--agda-type)">⌊5/3⌋ = 1 — greatest 3y ≤ 5</text>
  <text x="390" y="42" font-size="14" text-anchor="middle" fill="var(--agda-function)">⌈5/3⌉ = 2 — least 3y ≥ 5</text>
  <path d="M 272 100 Q 230 68 190 101" fill="none" stroke="var(--agda-type)" stroke-width="1.5" marker-end="url(#arrow)"/>
  <path d="M 288 100 Q 306 74 324 101" fill="none" stroke="var(--agda-function)" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="25" y1="110" x2="495" y2="110" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="88" y1="104" x2="88" y2="116" stroke="currentColor" opacity="0.4"/>
  <line x1="136" y1="104" x2="136" y2="116" stroke="currentColor" opacity="0.4"/>
  <line x1="232" y1="104" x2="232" y2="116" stroke="currentColor" opacity="0.4"/>
  <line x1="376" y1="104" x2="376" y2="116" stroke="currentColor" opacity="0.4"/>
  <line x1="424" y1="104" x2="424" y2="116" stroke="currentColor" opacity="0.4"/>
  <circle cx="40" cy="110" r="4.5" fill="currentColor"/>
  <circle cx="184" cy="110" r="4.5" fill="currentColor"/>
  <circle cx="328" cy="110" r="4.5" fill="currentColor"/>
  <circle cx="472" cy="110" r="4.5" fill="currentColor"/>
  <circle cx="280" cy="110" r="5.5" fill="none" stroke="currentColor" stroke-width="2"/>
  <text x="40" y="138" font-size="14" text-anchor="middle" fill="currentColor">0</text>
  <text x="184" y="138" font-size="14" text-anchor="middle" fill="currentColor">3</text>
  <text x="280" y="138" font-size="14" font-weight="bold" text-anchor="middle" fill="currentColor">x = 5</text>
  <text x="328" y="138" font-size="14" text-anchor="middle" fill="currentColor">6</text>
  <text x="472" y="138" font-size="14" text-anchor="middle" fill="currentColor">9</text>
  <text x="40" y="158" font-size="12" text-anchor="middle" fill="currentColor" opacity="0.65">3·0</text>
  <text x="184" y="158" font-size="12" text-anchor="middle" fill="currentColor" opacity="0.65">3·1</text>
  <text x="328" y="158" font-size="12" text-anchor="middle" fill="currentColor" opacity="0.65">3·2</text>
  <text x="472" y="158" font-size="12" text-anchor="middle" fill="currentColor" opacity="0.65">3·3</text>
</svg>
```

### A finite total order

The book's next exercise puts a Galois connection on the 3-element chain
$1 \leq 2 \leq 3$. Given the red map g with $g(1) = 2$, $g(2) = 2$,
$g(3) = 3$, the selection rule forces the blue f:

- $f(1) = 1$ and $f(2) = 1$: already $g(1) = 2$ is $\geq$ both 1 and 2, so the least good $q$ is 1;
- $f(3) = 3$: only $g(3)$ reaches 3.

Dually, $g(1) = 2$ because *both* $f(1)$ and $f(2)$ land $\leq 1$, and the
right adjoint takes the greatest such p. In a total order drawn this way,
f is left adjoint to g exactly when the bent arrows never cross.

```svg
<svg viewBox="0 0 440 250" role="img" aria-label="Two copies of the chain 1 up to 3, P above Q; blue dashed arrows show f mapping 1 and 2 to 1 and 3 to 3; red dashed arrows show g mapping 1 and 2 to 2 and 3 to 3; the bent arrows never cross">
  <text x="140" y="30" font-size="14" text-anchor="middle" fill="var(--agda-function)">f — left adjoint</text>
  <text x="320" y="30" font-size="14" text-anchor="middle" fill="var(--agda-type)">g — right adjoint</text>
  <text x="50" y="76" font-size="16" font-weight="bold" text-anchor="middle" fill="currentColor">P</text>
  <text x="130" y="76" font-size="16" text-anchor="middle" fill="currentColor">1</text>
  <text x="230" y="76" font-size="16" text-anchor="middle" fill="currentColor">2</text>
  <text x="330" y="76" font-size="16" text-anchor="middle" fill="currentColor">3</text>
  <line x1="142" y1="71" x2="216" y2="71" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="242" y1="71" x2="316" y2="71" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <text x="50" y="186" font-size="16" font-weight="bold" text-anchor="middle" fill="currentColor">Q</text>
  <text x="130" y="186" font-size="16" text-anchor="middle" fill="currentColor">1</text>
  <text x="230" y="186" font-size="16" text-anchor="middle" fill="currentColor">2</text>
  <text x="330" y="186" font-size="16" text-anchor="middle" fill="currentColor">3</text>
  <line x1="142" y1="181" x2="216" y2="181" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="242" y1="181" x2="316" y2="181" stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)"/>
  <path d="M 124 88 C 112 115 112 145 124 170" fill="none" stroke="var(--agda-function)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 224 88 Q 170 130 138 168" fill="none" stroke="var(--agda-function)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 324 88 C 312 115 312 145 324 170" fill="none" stroke="var(--agda-function)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 136 170 Q 190 130 222 90" fill="none" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 236 170 C 248 145 248 115 236 88" fill="none" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <path d="M 336 170 C 348 145 348 115 336 88" fill="none" stroke="var(--agda-type)" stroke-width="1.5" stroke-dasharray="5 4" marker-end="url(#arrow)"/>
  <text x="220" y="232" font-size="13" text-anchor="middle" fill="currentColor" opacity="0.75">adjoint pair ⇔ the bent arrows never cross</text>
</svg>
```
