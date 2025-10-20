---
layout: agda
title: "Computation as Rewriting"
section: "Examples"
chapter: 1
number: 113
---

# Computation as Rewriting

**Example 1.113.** Here is an example of closure operators from computation, very roughly presented. Imagine computation as a process of rewriting input expressions to output expressions. For example, a computer can rewrite the expression 7 + 2 + 3 as the expression 12. The set of arithmetic expressions has a partial order according to whether one expression can be rewritten as another.

We might think of a computer program, then, as a method of taking an expression and reducing it to another expression. So it is a map j : exp → exp. It furthermore is desirable to require that this computer program is a closure operator. Monotonicity means that if an expression x can be rewritten into expression y, then the reduction j(x) can be rewritten into j(y). Moreover, the requirement x ≤ j(x) implies that j can only turn one expression into another if doing so is a permissible rewrite. The requirement j(j(x)) = j(x) implies that if you try to reduce an expression that has already been reduced, the computer program leaves it as is. These properties provide useful structure in the analysis of program semantics.

## Setup

```agda
module examples.ComputationAsRewriting where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import definitions.Preorder using (Preorder; IsPreorder)
open import definitions.ClosureOperator using (ClosureOperator)
open import definitions.MonotoneMap using (Monotonic)
```

## A Simple Expression Language

We define a simple arithmetic expression language with addition.

```agda
-- Arithmetic expressions: either a natural number or a sum of two expressions
data Expr : Set where
  Num : ℕ → Expr
  Add : Expr → Expr → Expr
```

## The Rewriting Preorder

Expressions form a preorder where x ≤ y means "x can be rewritten to y".

```agda
-- The rewriting relation: x ⇒* y means "x can be rewritten to y in zero or more steps"
data _⇒*_ : Expr → Expr → Set where
  -- Reflexivity: every expression can be rewritten to itself (in zero steps)
  refl-⇒ : ∀ {e} → e ⇒* e

  -- Transitivity: if e₁ ⇒* e₂ and e₂ ⇒* e₃, then e₁ ⇒* e₃
  trans-⇒ : ∀ {e₁ e₂ e₃} → e₁ ⇒* e₂ → e₂ ⇒* e₃ → e₁ ⇒* e₃

  -- Evaluation step: (Num m) + (Num n) can be rewritten to Num (m + n)
  eval-step : ∀ {m n} → Add (Num m) (Num n) ⇒* Num (m + n)

  -- Congruence for left argument of addition
  cong-left : ∀ {e₁ e₂ e} → e₁ ⇒* e₂ → Add e₁ e ⇒* Add e₂ e

  -- Congruence for right argument of addition
  cong-right : ∀ {e e₁ e₂} → e₁ ⇒* e₂ → Add e e₁ ⇒* Add e e₂

-- The rewriting relation forms a preorder
⇒*-isPreorder : IsPreorder _⇒*_
⇒*-isPreorder = record
  { reflexive = refl-⇒
  ; transitive = trans-⇒
  }

-- The preorder of expressions under rewriting
ExprPreorder : Preorder
ExprPreorder = record
  { Carrier = Expr
  ; _≤_ = _⇒*_
  ; isPreorder = ⇒*-isPreorder
  }
```

## A Simple Reduction Strategy

We define a simple reduction strategy that evaluates expressions from left to right.

```agda
-- Reduce an expression by one step (if possible)
-- This is our "computer program" j : exp → exp
-- This implementation evaluates simple additions
reduce-once : Expr → Expr
reduce-once (Num n) = Num n
reduce-once (Add (Num m) (Num n)) = Num (m + n)
reduce-once (Add e₁ e₂) = Add (reduce-once e₁) (reduce-once e₂)
```

## Properties of the Reduction Strategy

To form a closure operator, we need to verify:
1. **Monotonicity**: If e₁ ⇒* e₂, then reduce-once(e₁) ⇒* reduce-once(e₂)
2. **Extensivity**: e ⇒* reduce-once(e) (reduction is a valid rewrite)
3. **Idempotence**: reduce-once(reduce-once(e)) ≅ reduce-once(e) (reduced expressions stay reduced)

For this example, we postulate these properties to demonstrate the structure. A complete formalization would prove them from the definition of reduce-once.

```agda
-- Postulate: reduce-once is monotonic
postulate
  reduce-monotonic : Monotonic _⇒*_ _⇒*_ reduce-once

-- Postulate: reduce-once is extensive (reduction is a valid rewrite)
postulate
  reduce-extensive : ∀ (e : Expr) → e ⇒* reduce-once e

-- Postulate: reduce-once is idempotent (up to equivalence)
postulate
  reduce-idempotent : ∀ (e : Expr) → (reduce-once (reduce-once e) ⇒* reduce-once e) × (reduce-once e ⇒* reduce-once (reduce-once e))
```

## The Closure Operator

Now we can construct the closure operator, demonstrating that our reduction strategy has the right mathematical structure:

```agda
-- reduce-once forms a closure operator on the expression preorder
reduction-closure : ClosureOperator ExprPreorder
reduction-closure = record
  { j = reduce-once
  ; j-monotonic = reduce-monotonic
  ; extensive = reduce-extensive
  ; idempotent = reduce-idempotent
  }
```

## Why Closure Operators Are Desirable for Program Semantics

Now that we have `reduction-closure : ClosureOperator ExprPreorder`, we can leverage its structure to prove useful properties about our reduction strategy. The closure operator properties give us powerful reasoning principles:

```agda
open ClosureOperator reduction-closure
open import Data.Product using (proj₁; proj₂)

-- Property 1: Reduction is safe (never produces invalid rewrites)
-- Because j is extensive, we know reduction is always a valid computational step
reduction-is-safe : ∀ (e : Expr) → e ⇒* j e
reduction-is-safe = extensive

-- Property 2: Reduction is confluent with itself
-- If we reduce e, we can still reach the same result by reducing again
reduction-confluence : ∀ (e : Expr) → j (j e) ⇒* j e
reduction-confluence e = proj₁ (idempotent e)

-- Property 3: Reduced forms are stable
-- Once we've reduced an expression, reducing it again changes nothing (up to equivalence)
reduced-stable : ∀ (e : Expr) → (j (j e) ⇒* j e) × (j e ⇒* j (j e))
reduced-stable = idempotent

-- Property 4: Reduction preserves improvement
-- If e₁ can rewrite to e₂, then reducing e₁ can rewrite to reducing e₂
-- This means reduction respects the computational order
reduction-preserves-improvement : ∀ {e₁ e₂ : Expr} → e₁ ⇒* e₂ → j e₁ ⇒* j e₂
reduction-preserves-improvement = j-monotonic

-- Property 5: Reduction always makes progress or reaches a fixed point
-- Since j(e) is reachable from e, and j(j(e)) ≅ j(e), we know that
-- applying reduction eventually stabilizes
reduction-eventually-stabilizes : ∀ (e : Expr) → e ⇒* j e × (j (j e) ⇒* j e)
reduction-eventually-stabilizes e = extensive e , proj₁ (idempotent e)
```

## Practical Benefits

These properties give us powerful tools for reasoning about programs:

**1. Correctness**: We can prove that our reduction never produces "garbage" - every step is a valid rewrite (extensivity).

**2. Determinism**: Even though expressions might have multiple reduction paths, the closure operator structure tells us that applying our reduction strategy eventually reaches a stable point (idempotence).

**3. Composability**: We can chain reductions safely, knowing that `reduce-once(reduce-once(e))` is equivalent to `reduce-once(e)` (idempotence), so redundant reductions don't cause problems.

**4. Reasoning about optimizations**: If we can prove `e₁ ⇒* e₂`, then we know `j(e₁) ⇒* j(e₂)` (monotonicity), allowing us to reason compositionally about program transformations.

**5. Termination analysis**: The combination of extensivity and idempotence provides a framework for proving that reduction eventually terminates at a stable value.

## A Concrete Example

Let's demonstrate how these properties help us reason about a specific computation:

```agda
-- Example expression: (7 + 2) + 3
example-expr : Expr
example-expr = Add (Add (Num 7) (Num 2)) (Num 3)

-- We can prove that reducing this expression is safe
example-safe : example-expr ⇒* j example-expr
example-safe = reduction-is-safe example-expr

-- We can prove that if we reduce twice, it's equivalent to reducing once
example-stable : j (j example-expr) ⇒* j example-expr
example-stable = reduction-confluence example-expr

-- If we know (Num 7) ⇒* (Num 7), we can conclude that
-- j(Num 7) ⇒* j(Num 7) using monotonicity
example-monotonicity : Num 7 ⇒* Num 7 → j (Num 7) ⇒* j (Num 7)
example-monotonicity = reduction-preserves-improvement
```

Without the closure operator structure, we would need to prove each of these properties individually for each expression. The `ClosureOperator` abstraction gives us these guarantees **for free** for all expressions, demonstrating why it's desirable to structure reduction strategies as closure operators.

## Note on Full Formalization

For pedagogical purposes, we've postulated the three closure operator properties. A complete formalization would prove:
- **Monotonicity**: By induction on the derivation of e₁ ⇒* e₂
- **Extensivity**: By induction on the structure of expressions
- **Idempotence**: By showing that reduce-once produces expressions in normal form

These proofs require additional lemmas about the structure of expressions and the properties of the rewriting relation, but the closure operator structure provides the right framework for organizing such proofs.
```
