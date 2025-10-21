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

Brief high-level summary of what we're constructing (1-2 sentences).

```agda
-- Key type signatures that show WHAT we're building
main-construction : InputType → OutputType

-- Any other important top-level definitions
helper-type : Set
helper-type = ...
```

### Implementation

**Strategy:** Brief description of how the construction works.

```agda
-- All implementation details here
main-construction input = result
  where
    helper : HelperType
    helper = ...

    result : OutputType
    result = ...
```

## [Optional: Additional Sections]

You can have additional sections if the example is complex. Each follows the same pattern:

```agda
-- Type signatures visible
another-construction : SomeType → ResultType
```

### Implementation

```agda
-- Implementation collapsed
another-construction input = ...
```

---

## Notes for using this template:

1. **Textbook Description** - Always collapsed by default.

2. **Agda Setup** - Always collapsed by default.

3. **The Example** - Main section showing WHAT is being constructed
   - Keep type signatures visible
   - Add brief explanatory text
   - Implementation details go in the "Implementation" subsection

4. **Implementation** (h3) - Always collapsed by default
   - Contains all proof/construction details
   - Include Strategy explanation
   - Can appear multiple times under different h2 sections

5. **Keep it concise** - The visible parts should give a quick overview
   - Type signatures tell the story
   - Brief prose explains the idea
   - Details are hidden but accessible

6. **Pattern to follow:**
   ```
   ## Section Title
   Brief explanation

   Type signatures (visible)

   ### Implementation
   Code (collapsed)
   ```

Example structure:

```markdown
## The Functors

Brief explanation of what functors we're defining.

```agda
f* : 𝒫B → 𝒫A
f! : 𝒫A → 𝒫B
f∗ : 𝒫A → 𝒫B
```

### Implementation

**Strategy:** How we define each functor.

```agda
f* B' a = B' (f a)
f! A' b = Σ[ a ∈ A ] (A' a × f a ≡ b)
f∗ A' b = ∀ {a} → f a ≡ b → A' a
```

## The Adjunctions

Brief explanation of the adjoint pairs.

```agda
f!⊆→⊆f* : ∀ {A' B'} → f! A' ⊆ B' → A' ⊆ f* B'
⊆f*→f!⊆ : ∀ {A' B'} → A' ⊆ f* B' → f! A' ⊆ B'
```

### Implementation

```agda
f!⊆→⊆f* f!A'⊆B' {a} a∈A' = f!A'⊆B' (a , a∈A' , refl)
⊆f*→f!⊆ A'⊆f*B' {b} (a , a∈A' , refl) = A'⊆f*B' a∈A'
```
```

7. **Narrative sections** (like Summary, Interpretation, Concrete Examples) don't need Implementation subsections - they stay fully visible.

8. **Goal**: Reader should understand the example in 30 seconds from the visible parts, then dive into details if interested.
