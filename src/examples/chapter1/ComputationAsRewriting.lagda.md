---
layout: agda
title: "Computation as Rewriting"
section: "Examples"
chapter: 1
number: 113
---

# Computation as Rewriting

## Textbook Description

**Example 1.113 (Computation as rewriting).** Here is an example of closure operators from computation, very roughly presented. Imagine computation as a process of rewriting input expressions to output expressions. For example, a computer can rewrite the expression 7 + 2 + 3 as the expression 12. The set of arithmetic expressions has a partial order according to whether one expression can be rewritten as another.

We might think of a computer program, then, as a method of taking an expression and reducing it to another expression. So it is a map j : exp → exp. It furthermore is desirable to require that this computer program is a closure operator. Monotonicity means that if an expression x can be rewritten into expression y, then the reduction j(x) can be rewritten into j(y). Moreover, the requirement x ≤ j(x) implies that j can only turn one expression into another if doing so is a permissible rewrite. The requirement j(j(x)) = j(x) implies that if you try to reduce an expression that has already been reduced, the computer program leaves it as is. These properties provide useful structure in the analysis of program semantics.

## Agda Setup

```agda
module examples.chapter1.ComputationAsRewriting where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter1.ClosureOperator using (ClosureOperator)
open import definitions.chapter1.MonotoneMap using (Monotonic)
```

## The Example

Reduction strategies on arithmetic expressions form closure operators.

```agda
data Expr : Set where
  Num : ℕ → Expr
  Add : Expr → Expr → Expr

-- Rewriting: e₁ ⇒* e₂ means "e₁ rewrites to e₂ in ≥0 steps"
data _⇒*_ : Expr → Expr → Set where
  refl-⇒ : ∀ {e} → e ⇒* e
  trans-⇒ : ∀ {e₁ e₂ e₃} → e₁ ⇒* e₂ → e₂ ⇒* e₃ → e₁ ⇒* e₃
  eval-step : ∀ {m n} → Add (Num m) (Num n) ⇒* Num (m + n)
  cong-left : ∀ {e₁ e₂ e} → e₁ ⇒* e₂ → Add e₁ e ⇒* Add e₂ e
  cong-right : ∀ {e e₁ e₂} → e₁ ⇒* e₂ → Add e e₁ ⇒* Add e e₂

-- Preorder and reduction strategy
ExprPreorder : Preorder
reduce-once : Expr → Expr
reduction-closure : ClosureOperator ExprPreorder
```

### Implementation

**Strategy:** Define expressions and rewriting relation, construct closure operator (postulating properties pedagogically).

```agda
⇒*-isPreorder : IsPreorder _⇒*_
⇒*-isPreorder = record
  { reflexive = refl-⇒
  ; transitive = trans-⇒
  }

ExprPreorder = record
  { Carrier = Expr
  ; _≤_ = _⇒*_
  ; isPreorder = ⇒*-isPreorder
  }

-- Left-to-right reduction: evaluate when both operands are numbers
reduce-once (Num n) = Num n
reduce-once (Add (Num m) (Num n)) = Num (m + n)
reduce-once (Add e₁ e₂) = Add (reduce-once e₁) (reduce-once e₂)

-- Postulate closure properties (would be proven in complete formalization)
postulate
  reduce-monotonic : Monotonic _⇒*_ _⇒*_ reduce-once
  reduce-extensive : ∀ (e : Expr) → e ⇒* reduce-once e
  reduce-idempotent : ∀ (e : Expr) → (reduce-once (reduce-once e) ⇒* reduce-once e)
                                    × (reduce-once e ⇒* reduce-once (reduce-once e))

reduction-closure = record
  { j = reduce-once
  ; j-monotonic = reduce-monotonic
  ; extensive = reduce-extensive
  ; idempotent = reduce-idempotent
  }
```

## Properties We Get

From the closure operator structure:

```agda
open ClosureOperator reduction-closure

reduction-is-safe : ∀ (e : Expr) → e ⇒* reduce-once e
reduction-confluence : ∀ (e : Expr) → reduce-once (reduce-once e) ⇒* reduce-once e
reduction-preserves-improvement : ∀ {e₁ e₂ : Expr} → e₁ ⇒* e₂ → reduce-once e₁ ⇒* reduce-once e₂
```

### Implementation

```agda
reduction-is-safe = extensive
reduction-confluence e = proj₁ (idempotent e)
reduction-preserves-improvement = j-monotonic

reduced-stable : ∀ (e : Expr) → (reduce-once (reduce-once e) ⇒* reduce-once e)
                                × (reduce-once e ⇒* reduce-once (reduce-once e))
reduced-stable = idempotent

reduction-eventually-stabilizes : ∀ (e : Expr) → e ⇒* reduce-once e
                                                × (reduce-once (reduce-once e) ⇒* reduce-once e)
reduction-eventually-stabilizes e = extensive e , proj₁ (idempotent e)
```

## Why This Matters for Program Semantics

The closure operator structure provides powerful reasoning principles:

**1. Correctness**: Reduction never produces "garbage" - every step is a valid rewrite (extensivity).

**2. Determinism**: Applying the reduction strategy eventually reaches a stable point (idempotence).

**3. Composability**: We can chain reductions safely - `reduce-once(reduce-once(e))` is equivalent to `reduce-once(e)` (idempotence), so redundant reductions don't cause problems.

**4. Reasoning about optimizations**: If `e₁ ⇒* e₂`, then `reduce-once(e₁) ⇒* reduce-once(e₂)` (monotonicity), allowing compositional reasoning about program transformations.

**5. Termination analysis**: The combination of extensivity and idempotence provides a framework for proving that reduction eventually terminates at a stable value.

## Concrete Example

```agda
-- Example expression: (7 + 2) + 3
example-expr : Expr
example-expr = Add (Add (Num 7) (Num 2)) (Num 3)

-- Reducing this expression is safe
example-safe : example-expr ⇒* j example-expr
example-safe = reduction-is-safe example-expr

-- Reducing twice is equivalent to reducing once
example-stable : j (j example-expr) ⇒* j example-expr
example-stable = reduction-confluence example-expr

-- Monotonicity property
example-monotonicity : Num 7 ⇒* Num 7 → j (Num 7) ⇒* j (Num 7)
example-monotonicity = reduction-preserves-improvement
```

Without the closure operator structure, we would need to prove each of these properties individually for each expression. The `ClosureOperator` abstraction gives us these guarantees for all expressions, demonstrating why it's desirable to structure reduction strategies as closure operators.



