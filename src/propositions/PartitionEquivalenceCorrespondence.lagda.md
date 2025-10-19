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
open import plumbing.ClassicalPostulates using (_/_; [_]; quotient-sound; quotient-surjective; quotient-effective)
```

## Direction 1: Partition to Equivalence Relation

**Strategy:** Given a partition, define a ∼ b to mean "a and b are in the same part."

This is the easier direction—we just need to check that ∼ is reflexive, symmetric, and transitive.

```agda
partition→equivalence : {A : Set} → Partition A → Σ[ _∼_ ∈ BinRel A ] (IsEquivalence _∼_)
```

### Proof

```agda
partition→equivalence {A} π = _∼_ , is-equivalence
  where
    open Partition π

    -- Two elements are equivalent if they are in the same part
    _∼_ : BinRel A
    a ∼ b = Σ[ p ∈ P ] (A[ p ] a × A[ p ] b)

    -- This relation is an equivalence relation
    is-equivalence : IsEquivalence _∼_
    is-equivalence = record
      { reflexive = λ {a} →
          -- a is in the same part as itself
          let (p , a∈p) = union a
          in p , (a∈p , a∈p)
      ; symmetric = λ (p , (a∈p , b∈p)) →
          -- if a is in the same part as b, then b is in the same part as a
          p , (b∈p , a∈p)
      ; transitive = λ {a} {b} {c} (p , (a∈p , b∈p)) (q , (b∈q , c∈q)) →
          -- if a is in the same part as b and b is in the same part as c,
          -- then a is in the same part as c
          -- Since b is in both part p and part q, we have p ≡ q by uniqueness
          let p≡q = unique b∈p b∈q
          in p , (a∈p , subst (λ r → A[ r ] c) (sym p≡q) c∈q)
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

A disadvantage of agda is you can't 

The **quotient type** A/∼ represents "the set of all equivalence classes."
- Each element q : A/∼ represents one equivalence class
- We can extract a representative: quotient-surjective gives us some a with [a] ≡ q

```agda
    partition : Partition A
    partition = record
      { P = A / _∼_  -- Labels: one for each equivalence class

      ; A[_] = λ q →
          -- Given a label q, return its equivalence class
          -- Extract any representative rep where [rep] ≡ q
          let (rep , _) = quotient-surjective q
          in ⟦ rep ⟧

      ; nonempty = λ q →
          -- Each part is nonempty
          let (rep , _) = quotient-surjective q
          in rep , reflexive

      ; union = λ a →
          -- Every element a is in some part
          -- The part is labeled by [ a ], the equivalence class containing a
          let (rep , [rep]≡[a]) = quotient-surjective {_∼_ = _∼_} [ a ]
              rep∼a = quotient-effective {_∼_ = _∼_} [rep]≡[a]
              a∼rep = symmetric rep∼a
          in [ a ] , a∼rep

      ; unique = λ {a} {p} {q} a∈p a∈q →
          -- If a is in part p and part q, then p ≡ q
          -- Key insight: a∈p means a ∼ rep-p, a∈q means a ∼ rep-q
          -- So rep-p ∼ rep-q, thus their equivalence classes are equal
          let (rep-p , [rep-p]≡p) = quotient-surjective {_∼_ = _∼_} p
              (rep-q , [rep-q]≡q) = quotient-surjective {_∼_ = _∼_} q
              rep-p∼a = symmetric a∈p
              rep-p∼rep-q = transitive rep-p∼a a∈q
              [rep-p]≡[rep-q] = quotient-sound {_∼_ = _∼_} rep-p∼rep-q
          in trans (sym [rep-p]≡p) (trans [rep-p]≡[rep-q] [rep-q]≡q)
      }
```