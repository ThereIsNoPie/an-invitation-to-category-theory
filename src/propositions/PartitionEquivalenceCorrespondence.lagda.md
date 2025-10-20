---
layout: agda
title: "Partition-Equivalence Correspondence"
section: "Propositions"
chapter: 1
number: 14
---

# Partition-Equivalence Correspondence

**Proposition 1.14.** Let A be a set. There is a one-to-one correspondence between the ways to partition A and the equivalence relations on A.

## Intuition

- Partition → Equivalence: "a ∼ b" means "a and b are in the same part"
- Equivalence → Partition: "the parts are the equivalence classes"

## Setup

```agda
module propositions.PartitionEquivalenceCorrespondence where

open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; _,_)
open import Data.Empty using (⊥-elim; ⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
open import Relation.Nullary using (¬_)

open import definitions.Partition using (Partition; Subset)
open import definitions.EquivalenceRelation using (IsEquivalence)
open import definitions.Relation using (BinRel)
-- Note: definitions.Quotient defines quotients as Subset A (predicative)
-- We use the impredicative quotient type from ClassicalPostulates for this proof
open import plumbing.ClassicalPostulates using (_/_; [_]; quotient-sound; quotient-surjective; quotient-effective)
```

## Direction 1: Partition to Equivalence Relation

**Strategy:** Given a partition, define a ∼ b to mean "a and b are in the same part."

This is the easier direction—we just need to check that ∼ is reflexive, symmetric, and transitive.

```agda
partition→equivalence : {A : Set} → Partition A → Σ[ _∼_ ∈ BinRel A ] (IsEquivalence _∼_)
```

### Proof Strategy

We define: **a ∼ b** means "there exists a part p containing both a and b"

Then we verify this is reflexive, symmetric, and transitive.

```agda
partition→equivalence {A} π = _∼_ , is-equivalence
  where
    open Partition π

    -- DEFINITION: Two elements are equivalent if they share a part
    _∼_ : BinRel A
    a ∼ b = Σ[ p ∈ P ] (A[ p ] a × A[ p ] b)
    --      └─────┬─────┘  └────┬────┘
    --        "some part p"   "a proof `a` is in p AND a proof `b` is in p"

    -- Reflexive: a ∼ a (every element is in the same part as itself)
    reflexive-proof : ∀ {a} → a ∼ a
    reflexive-proof {a} =
      let (p , a∈p) = union a -- in the definition of partition, "union" says a is in some part p
          in p , (a∈p , a∈p) -- use that proof to prove "a is in p AND a is in p"

    -- Symmetric: if a ∼ b then b ∼ a (if a and b are in the same part, then b and a are in the same part)
    symmetric-proof : ∀ {a b} → a ∼ b → b ∼ a
    symmetric-proof (p , (a-in-p , b-in-p)) =
      p , (b-in-p , a-in-p)  -- Just swap the order!

    -- Transitive: if a ∼ b and b ∼ c then a ∼ c
    transitive-proof : ∀ {a b c} → a ∼ b → b ∼ c → a ∼ c
    transitive-proof {a} {b} {c} a∼b b∼c =
      let
          (p , (a∈p , b∈p)) = a∼b -- p is the part containing a and b
          (q , (b∈q , c∈q)) = b∼c -- q is the part containing b and c
          p≡q = unique b∈p b∈q -- b is in both p and q, so they must be the same part
          c∈p = subst (λ part → A[ part ] c) (sym p≡q) c∈q -- if c is in q and p ≡ q, then c is in p
      in p , (a∈p , c∈p)

    -- PROOF: This is reflexive, symmetric, and transitive
    is-equivalence : IsEquivalence _∼_
    is-equivalence = record
      { reflexive = reflexive-proof
      ; symmetric = symmetric-proof
      ; transitive = transitive-proof
      }
```

## Direction 2: Equivalence Relation to Partition

**Strategy:** Given an equivalence relation ∼, the parts are the equivalence classes.

This is the harder direction. We need to:
1. Define what the "parts" are (equivalence classes)
2. Choose labels for the parts (the quotient type A/∼)
3. Verify the partition properties (nonempty, union, unique)

```agda
equivalence→partition : {A : Set} (_∼_ : BinRel A) → IsEquivalence _∼_ → Partition A
```

### Step 1: Define equivalence classes

The **equivalence class** of an element a is the set of all elements related to a.

```agda
equivalence→partition {A} _∼_ equiv = partition
  where
    open IsEquivalence equiv
    open import plumbing.EquationalReasoning using (module ∼-Reasoning; module ≡-Reasoning)

    -- The equivalence class of an element a
    -- ⟦ a ⟧ = { x ∈ A | x ∼ a }
    ⟦_⟧ : A → Subset A
    ⟦ a ⟧ = λ x → x ∼ a
```

### Step 2: Verify equivalence classes form valid parts

We need to show equivalence classes are both **closed** and **connected**.

**Closed** means: if x is in the class and x′ ∼ x, then x′ is also in the class.
**Connected** means: any two elements in the class are related.

```agda
    -- A subset X ⊆ A is (∼)-closed if: x ∈ X and x′ ∼ x implies x′ ∈ X
    IsClosed : Subset A → Set
    IsClosed X = ∀ {x x′} → X x → x′ ∼ x → X x′

    -- A subset X ⊆ A is (∼)-connected if it's nonempty and any two elements are related
    IsConnected : Subset A → Set
    IsConnected X = Σ[ a ∈ A ] (X a) × (∀ {x y} → X x → X y → x ∼ y)

    -- A part is both closed and connected
    IsPart : Subset A → Set
    IsPart X = IsClosed X × IsConnected X

    -- Prove that equivalence classes satisfy these properties
    ⟦⟧-closed : ∀ a → IsClosed ⟦ a ⟧
    ⟦⟧-closed a x∼a x′∼x = transitive x′∼x x∼a

    ⟦⟧-connected : ∀ a → IsConnected ⟦ a ⟧
    ⟦⟧-connected a = a , reflexive , λ x∼a y∼a → transitive x∼a (symmetric y∼a)

    ⟦⟧-is-part : ∀ a → IsPart ⟦ a ⟧
    ⟦⟧-is-part a = ⟦⟧-closed a , ⟦⟧-connected a
```

### Step 3: Build the partition using quotient types

**Note on quotients:** Definition 1.16 defines the quotient `Quotient A _∼_` as a synonym for `Subset A`, representing quotients as predicates. However, to prove this proposition, we need the stronger **quotient type** with computational content from `plumbing.ClassicalPostulates`.

The **quotient type** A/∼ (written `A / _∼_`) represents "the set of all equivalence classes" as a Set (not Set₁). It provides:
- A type `A / _∼_ : Set` of equivalence class labels
- A function `[_] : A → A / _∼_` that maps elements to their class
- `quotient-sound`: if a ∼ b then [a] ≡ [b]
- `quotient-effective`: if [a] ≡ [b] then a ∼ b
- `quotient-surjective`: every label has a representative

This quotient type lives at the same universe level as A, which is essential for constructing `P : Set` in the partition. Without this postulate, the partition's index type would live in Set₁, violating the definition.

```agda
    partition : Partition A
    partition = record
      { P = A / _∼_
      ; A[_] = get-part
      ; nonempty = nonempty-proof
      ; union = union-proof
      ; unique = unique-proof
      }
      where
        -- Given a label q : A/∼, what is the corresponding part?
        -- Answer: the equivalence class of any representative
        get-part : (A / _∼_) → Subset A
        get-part q =
          let (rep , _) = quotient-surjective q
          in ⟦ rep ⟧

        -- Prove each part is nonempty
        nonempty-proof : ∀ (q : A / _∼_) → Σ[ a ∈ A ] (get-part q a)
        nonempty-proof q =
          let (rep , _) = quotient-surjective q
          in rep , reflexive  -- rep ∼ rep 

        -- Prove every element is in some part
        union-proof : ∀ (a : A) → Σ[ q ∈ (A / _∼_) ] (get-part q a)
        union-proof a =
          let label : A / _∼_
              label = [ a ]  

              (rep , [rep]≡[a]) = quotient-surjective {_∼_ = _∼_} label
              rep~a = quotient-effective {_∼_ = _∼_} [rep]≡[a]
              a∼rep = symmetric rep~a
          in label , a∼rep

        -- Prove if a is in two parts, those parts are equal
        unique-proof : ∀ {a : A} {p q : A / _∼_} →
                       get-part p a → get-part q a → p ≡ q
        unique-proof {a} {p} {q} a∈p a∈q =
          let -- Extract representatives for p and q
              (rep-p , [rep-p]≡p) = quotient-surjective {_∼_ = _∼_} p
              (rep-q , [rep-q]≡q) = quotient-surjective {_∼_ = _∼_} q

              -- Use ∼-Reasoning to show rep-p ∼ rep-q
              open ∼-Reasoning _∼_ reflexive symmetric transitive
                renaming (begin_ to begin∼_; _∎ to _∎∼)
              rep-p∼rep-q : rep-p ∼ rep-q
              rep-p∼rep-q =
                begin∼
                  rep-p   ∼⟨ symmetric a∈p ⟩   -- a ∼ rep-q
                  a       ∼⟨ a∈q ⟩
                  rep-q   ∎∼

              [rep-p]≡[rep-q] = quotient-sound {_∼_ = _∼_} rep-p∼rep-q

              open ≡-Reasoning
          in begin
               p           ≡˘⟨ [rep-p]≡p ⟩     -- p ≡ [rep-p]
               [ rep-p ]   ≡⟨ [rep-p]≡[rep-q] ⟩  -- [rep-p] ≡ [rep-q]
               [ rep-q ]   ≡⟨ [rep-q]≡q ⟩        -- [rep-q] ≡ q
               q           ∎
```