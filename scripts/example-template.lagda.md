---
layout: agda
title: "Your Example Title"
section: "Examples"
chapter: 1
number: XXX
---

# Your Example Title

## Textbook Description

**Example 1.XXX (Your example name).** State the example description here, exactly as it appears in the textbook. This section provides intuition and context for what we're demonstrating.

## Agda Setup

```agda
module examples.YourExampleName where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Add other necessary imports
```

## The Example

Brief high-level explanation of what we're constructing.

### Key Type Definitions

Define any important types that are central to the example:

```agda
-- Core type definitions
DataType : Set
DataType = ...

-- Important type aliases or specialized types
AnotherType : Set
AnotherType = ...
```

## Main Construction

Brief description of what we're building.

Type signatures for what we're constructing (visible):

```agda
main-function : InputType → OutputType

helper-function : HelperInputType → HelperOutputType
```

### Implementation

**Strategy:** Brief description of how the implementation works.

```agda
-- Implementation details here
main-function input = result
  where
    helper : HelperType
    helper = ...

    result : OutputType
    result = ...

helper-function input = ...
```

## Properties We Get For Free

Brief explanation of what properties follow from the main construction.

Type signatures for properties (visible):

```agda
property-1 : ∀ (x : Type) → PropertyType

property-2 : ∀ (x y : Type) → AnotherPropertyType
```

### Implementation

**Strategy:** How these properties follow from the main construction.

```agda
-- Proofs/implementations
property-1 x = ...
  where
    -- Use main-function here
    ...

property-2 x y = ...
```

## [Optional: Additional Constructions/Properties]

You can have multiple sections following the same pattern:
- Section heading
- Type signatures (visible)
- Implementation subsection (collapsed)

For example:

## Another Construction

Brief description.

```agda
another-thing : SomeType → ResultType
```

### Implementation

```agda
another-thing input = ...
```

## [Optional: Concrete Example]

Demonstrate the constructions with specific values:

```agda
-- Concrete data
example-input : InputType
example-input = ...

-- Applying our construction
example-result : OutputType
example-result = main-function example-input
```

## [Optional: Interpretation/Summary]

Explain the significance of what was constructed and how it connects to broader theory.

---

## Notes for using this template:

1. **Textbook Description** - Always collapsed by default.

2. **Agda Setup** - Always collapsed by default.

3. **Pattern for each major section:**
   ```
   ## Section Title
   Brief overview

   Type signatures (visible)

   ### Implementation
   Code (collapsed)
   ```

4. This pattern can repeat multiple times:
   - **Main Construction** + Implementation
   - **Properties** + Implementation
   - **Another Construction** + Implementation
   - etc.

5. The key insight: Each h2 section can have its own h3 "Implementation" subsection that gets collapsed, while the type signatures remain visible.

6. **Implementation** headings (h3) will be collapsed automatically by the layout.

7. Examples of section titles:
   - "Main Construction"
   - "Properties We Get For Free"
   - "Verification"
   - "The Adjunction"
   - "Direction 1" / "Direction 2" (for bidirectional constructions)

8. Narrative sections without implementations (like "Interpretation", "Concrete Example", "Summary") don't need an Implementation subsection and remain fully visible.
