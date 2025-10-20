---
layout: agda
title: "Your Proposition Title"
section: "Propositions"
chapter: 1
number: XX
---

# Your Proposition Title

## Textbook Definition

**Proposition 1.XX.** State the proposition here in natural language, exactly as it appears in the textbook.

## Agda Setup

```agda
module propositions.YourPropositionName where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Add other necessary imports
```

## Proposition

State what you're proving (optional high-level description).

```agda
your-proposition-name : {A : Set} → PremiseType → ConclusionType
```

## Proof

**Strategy:** Brief description of the proof strategy (optional).

```agda
your-proposition-name premise = result
  where
    -- Proof implementation here
    helper : HelperType
    helper = ...

    result : ConclusionType
    result = ...
```

---

## Notes for using this template:

1. **Textbook Definition** - Always include this heading. It will be collapsed by default in the HTML.

2. **Agda Setup** - Always use this exact heading name (not "Setup"). It will be collapsed by default.

3. **Proposition** - This section contains just the type signature. Keep it visible so readers can see what you're proving.

4. **Proof** - This heading will be collapsed by default. All proof implementation goes here.

5. For propositions with multiple parts/directions:
   - Use h3 (###) for sub-parts under the main Proof section
   - Or create separate "Proof: Part 1", "Proof: Part 2" sections (both will collapse)

Example structure for multi-part propositions:

```markdown
## Proposition

```agda
part1 : A → B
part2 : B → A
```

## Proof: Part 1

```agda
part1 x = ...
```

## Proof: Part 2

```agda
part2 y = ...
```