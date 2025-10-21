---
layout: agda
title: "Your Exercise Title"
section: "Exercises"
chapter: 1
number: XXX
---

# Your Exercise Title

## Textbook Exercise

**Exercise 1.XXX.** State the exercise problem here in natural language, exactly as it appears in the textbook.

## Agda Setup

```agda
module exercises.YourExerciseName where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Add other necessary imports
```

## Problem

Brief explanation of what we're solving (optional).

```agda
module _ (parameters : ParameterTypes) where
  private
    -- Any helper definitions or open statements needed for the type signature
    -- ...

  -- The exercise: just the type signature(s)
  exercise-name : {A : Set} → PremiseType → ConclusionType
```

## Solution

**Strategy:** Brief description of the solution approach (optional).

```agda
  -- Any additional open statements needed for the implementation
  -- ...

  -- The implementation (continuing in the same module)
  exercise-name premise = result
    where
      -- Solution implementation here
      helper : HelperType
      helper = ...

      result : ConclusionType
      result = ...
```

---

## Notes for using this template:

1. **Exercise** - Always include this heading with the textbook problem statement. It will remain visible.

2. **Agda Setup** - Always use this exact heading name. It will be collapsed by default.

3. **Problem** - This section contains just the type signature(s). Keep it visible so readers can see what they need to solve.
   - Use `module _ (parameters) where` to start the module
   - Include any `private` helper definitions or `open` statements needed for the type signature
   - List only the type signatures, NOT the implementations

4. **Solution** - This heading will be collapsed by default. All solution implementation goes here.
   - Continue in the SAME module (do NOT start a new module)
   - Add any additional `open` statements needed for the implementation
   - Provide the actual implementation/proof
   - The code block continues from the Problem section (note the indentation)

5. **IMPORTANT**: The Problem and Solution sections are in the SAME module. The split is purely visual:
   - Problem section: Type signatures only (visible to reader)
   - Solution section: Implementations only (collapsed by default)

   Example:
   ```markdown
   ## Problem
   ```agda
   module _ (P : Type) where
     foo : P → P
   ```

   ## Solution
   ```agda
     foo x = x  -- Note: continuing in the same module, same indentation
   ```
   ```

6. For exercises with multiple parts:
   - List all type signatures in the Problem section
   - Provide all implementations in the Solution section
   - You can optionally use h3 (###) subsections within Solution for organization
   - Or create separate "Solution: Part 1", "Solution: Part 2" sections (both will collapse)

7. **Goal**: Reader should be able to:
   - Read the problem statement
   - See the type signature and understand what needs to be proved
   - Attempt the exercise themselves
   - Expand the solution to check their work or get hints

8. Keep the visible parts minimal - just the problem statement and type signature.