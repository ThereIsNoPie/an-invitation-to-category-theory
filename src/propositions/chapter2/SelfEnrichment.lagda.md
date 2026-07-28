---
layout: agda
title: "A Closed V is Enriched in Itself"
section: "Propositions"
chapter: 2
number: 65
---

# A Closed V is Enriched in Itself

## Textbook Statement

**Remark 2.65.** We can consider $\mathcal{V}$ to be enriched in itself. That is, for every $v, w \in \mathrm{Ob}(\mathcal{V})$, we can define $\mathcal{V}(v, w) := (v \multimap w) \in \mathcal{V}$. For this to really be an enrichment, we just need to check the two conditions of Definition 2.30. The first condition $I \leq \mathcal{X}(x, x) = (x \multimap x)$ is satisfied because $I \otimes x \leq x$. The second condition is satisfied by Proposition 2.64(e).

## Agda Setup

```agda
module propositions.chapter2.SelfEnrichment where

open import definitions.chapter2.VCategory using (VCategory)
open import definitions.chapter2.MonoidalClosed using (MonoidalClosedPreorder)
open import propositions.chapter2.ClosedMonoidalProperties using (module Properties)
open import Relation.Binary.PropositionalEquality using (sym; subst)
```

## Statement

Every symmetric monoidal *closed* preorder is a category enriched in itself.
The objects are the elements of $\mathcal{V}$, and the hom-object of $v$ and $w$
is their internal hom $v \multimap w$.

```agda
-- Objects are elements of V; the hom-object of v, w is v ⊸ w.
self-enriched : (MCP : MonoidalClosedPreorder)
              → VCategory (MonoidalClosedPreorder.base MCP)
```

The two V-category axioms of Definition 2.30 land on results we already have:

- **Identity** `I ≤ (x ⊸ x)`: transpose `I ⊗ x = x ≤ x` across the closure
  adjunction with `curry`.
- **Composition** `(x ⊸ y) ⊗ (y ⊸ z) ≤ (x ⊸ z)`: this is exactly
  `hom-compose`, Proposition 2.64(e) — "converters compose".

## Proof

```agda
self-enriched MCP = record
  { Ob          = Carrier
  ; hom         = _⊸_
    -- I ≤ (x ⊸ x), because I ⊗ x = x ≤ x
  ; identity    = λ {x} → curry (subst (_≤ x) (sym left-unit) reflexive)
    -- exactly Proposition 2.64(e)
  ; composition = hom-compose
  }
  where
    open MonoidalClosedPreorder MCP
    open Properties MCP using (hom-compose)
```

## Interpretation

Up to now the "hom" of a V-category has been *external*: a hom-object living in
some separate base $\mathcal{V}$. Here $\mathcal{V}$'s own internal hom
$\multimap$ **is** the enrichment — $\mathcal{V}$ is a $\mathcal{V}$-category.

This is why Proposition 2.64(c)–(e) were worth proving: they are the enrichment
laws in disguise. In particular the resource reading of 2.64(e) — "a single-use
$u$-to-$v$ converter and a single-use $v$-to-$w$ converter compose into a
$u$-to-$w$ converter" — is *literally* the composition law of the resulting
category. Closedness is essential: a general symmetric monoidal preorder has no
$\multimap$ to serve as its hom-object, so it need not be self-enriched.
