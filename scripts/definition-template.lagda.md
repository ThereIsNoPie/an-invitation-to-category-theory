---
layout: agda
title: "Your Definition Title"
section: "Definitions"
chapter: 1
number: XX
---

# Your Definition Title

## Textbook Definition

**Definition 1.XX.** State the definition here in natural language, exactly as it appears in the textbook. Include all parts, conditions, and terminology introduced.

If the definition has multiple parts (a), (b), (c), preserve that structure.

## Agda Formalization

```agda
module definitions.YourDefinitionName where

-- Import dependencies
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Add other necessary imports (e.g., other definitions)
-- open import definitions.Preorder using (Preorder)

-- Formalize the definition in Agda
-- This can be a record type, a type alias, a function, etc.

-- Example for a record-based definition:
record YourDefinition : Set where
  field
    -- (a) First condition with comment referring to textbook
    condition1 : Type1

    -- (b) Second condition with comment referring to textbook
    condition2 : Type2

-- Example for a type alias definition:
YourType : Set → Set
YourType A = A → A  -- explanation

-- Example for a predicate/property definition:
IsYourProperty : {A : Set} → (A → A → Set) → Set
IsYourProperty _R_ = ∀ {x y} → x R y → SomeProperty

-- Derived properties or helper functions (if any)
-- These should be kept minimal - put derived theorems in propositions
```

---

## Notes for using this template:

1. **Textbook Definition** - Always collapsed by default. Copy the definition exactly as stated in the textbook.

2. **Agda Formalization** - This section is always visible (NOT collapsed) because definitions are meant to be referenced and used throughout the codebase.

3. **Structure patterns** for different kinds of definitions:

   **Record-based definitions** (e.g., Preorder, GaloisConnection):
   ```agda
   record YourDefinition (params : Types) : Set where
     field
       component1 : Type1
       component2 : Type2

     -- Derived properties go here (if simple)
   ```

   **Type aliases** (e.g., MonotoneMap, PartialOrder):
   ```agda
   YourType : Params → Set
   YourType params = Implementation
   ```

   **Predicates/Properties** (e.g., IsPreorder, Monotonic):
   ```agda
   IsYourProperty : {A : Set} → (A → A → Set) → Set
   IsYourProperty _R_ = ∀ {x y} → Conditions
   ```

4. **Comments in code** should:
   - Reference textbook parts: `-- (a) Reflexivity: x ≤ x`
   - Explain technical choices when Agda differs from math notation
   - Be concise - let the code speak

5. **Imports**:
   - Import from Agda standard library as needed
   - Import other definitions from `definitions.*` modules
   - Keep imports minimal and relevant

6. **Derived properties**:
   - Simple derived properties can go in the definition file
   - Non-trivial theorems should be separate propositions
   - Example: In GaloisConnection, `f-monotonic` and `g-monotonic` are derived from the adjunction

7. **Keep it clean**:
   - Definitions should be straightforward encodings of textbook definitions
   - Avoid unnecessary abstraction or generalization
   - The goal is clarity and correspondence to the textbook

8. **Naming conventions**:
   - Module name: `definitions.YourDefinitionName` (PascalCase)
   - Type names: PascalCase or mixfix (e.g., `_⇒_`)
   - Field names: camelCase or kebab-case
   - Follow Agda standard library conventions where applicable

Example minimal definition:

```markdown
# Reflexive Relation

## Textbook Definition

**Definition 1.XX.** A binary relation R on a set X is *reflexive* if for all x ∈ X, we have x R x.

## Agda Formalization

```agda
module definitions.ReflexiveRelation where

-- A relation R on a set A is reflexive if x R x for all x
IsReflexive : {A : Set} → (A → A → Set) → Set
IsReflexive _R_ = ∀ {x} → x R x
```
```

Example record-based definition:

```markdown
# Monoid

## Textbook Definition

**Definition 1.XX.** A *monoid* is a set M together with:

(a) A binary operation · : M × M → M

(b) An identity element e ∈ M such that e · x = x and x · e = x for all x ∈ M

(c) The operation is associative: (x · y) · z = x · (y · z) for all x, y, z ∈ M

## Agda Formalization

```agda
module definitions.Monoid where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Monoid : Set₁ where
  field
    Carrier : Set

    -- (a) Binary operation
    _·_ : Carrier → Carrier → Carrier

    -- (b) Identity element
    ε : Carrier

    -- Identity laws
    left-identity  : ∀ {x} → ε · x ≡ x
    right-identity : ∀ {x} → x · ε ≡ x

    -- (c) Associativity
    associative : ∀ {x y z} → (x · y) · z ≡ x · (y · z)
```
```
