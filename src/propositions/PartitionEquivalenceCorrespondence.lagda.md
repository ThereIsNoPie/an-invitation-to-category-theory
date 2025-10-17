---
layout: agda
title: "Partition-Equivalence Correspondence"
section: "Propositions"
chapter: 1
number: 14
---

# Partition-Equivalence Correspondence

**Proposition 1.14.** Let A be a set. There is a one-to-one correspondence between the ways to partition A and the equivalence relations on A.

## Setup

```agda
module propositions.PartitionEquivalenceCorrespondence where

open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; _,_)
open import Data.Empty using (⊥-elim; ⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Relation.Nullary using (¬_)

open import definitions.Partition using (Partition; Subset)
open import definitions.EquivalenceRelation using (IsEquivalence)
open import definitions.Relation using (BinRel)
```

## Partition to Equivalence Relation

From a partition to an equivalence relation: define a ∼ b if a and b are in the same part.

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

    -- Helper: if an element is in two parts, the parts must be equal
    -- (by contrapositive of disjointness)
    postulate
      unique-part : ∀ {a p q} → A[ p ] a → A[ q ] a → p ≡ q

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
          -- Since b is in both part p and part q, we have p ≡ q
          let p≡q = unique-part b∈p b∈q
          in p , (a∈p , subst (λ r → A[ r ] c) (sym p≡q) c∈q)
      }
```

## Equivalence Relation to Partition

From an equivalence relation to a partition: the parts are (∼)-closed, (∼)-connected subsets.

```agda
equivalence→partition : {A : Set} (_∼_ : BinRel A) → IsEquivalence _∼_ → Partition A
```

### Proof

```agda
equivalence→partition {A} _∼_ equiv = partition
  where
    open IsEquivalence equiv

    -- A subset X ⊆ A is (∼)-closed if for every x ∈ X and x′ ∼ x, we have x′ ∈ X
    IsClosed : Subset A → Set
    IsClosed X = ∀ {x x′} → X x → x′ ∼ x → X x′

    -- A subset X ⊆ A is (∼)-connected if it is nonempty and x ∼ y for every x, y ∈ X
    IsConnected : Subset A → Set
    IsConnected X = Σ[ a ∈ A ] (X a) × (∀ {x y} → X x → X y → x ∼ y)

    -- A part is a (∼)-closed, (∼)-connected subset
    IsPart : Subset A → Set
    IsPart X = IsClosed X × IsConnected X

    -- The equivalence class of an element a
    [_] : A → Subset A
    [ a ] = λ x → x ∼ a

    -- The equivalence class is closed
    []-closed : ∀ a → IsClosed [ a ]
    []-closed a x∼a x′∼x = transitive x′∼x x∼a

    -- The equivalence class is connected
    []-connected : ∀ a → IsConnected [ a ]
    []-connected a = a , reflexive , λ x∼a y∼a → transitive x∼a (symmetric y∼a)

    -- The equivalence class is a part
    []-is-part : ∀ a → IsPart [ a ]
    []-is-part a = []-closed a , []-connected a

    -- The parts form a partition
    partition : Partition A
    partition = record
      { P = A
      ; A[_] = [_]
      ; nonempty = λ p → p , reflexive
      ; union = λ a → a , reflexive
      ; disjoint = λ {p} {q} p≢q {a} (a∼p , a∼q) →
          -- If a ∼ p and a ∼ q, then by transitivity and symmetry: p ∼ q
          -- This means p and q are in the same equivalence class
          -- In set theory, this would imply p ≡ q, contradicting p ≢ q
          let p∼q = transitive (symmetric a∼p) a∼q
              q∼p = symmetric p∼q
          in postulate-disjoint p q p≢q p∼q q∼p
      }
      where
        postulate
          postulate-disjoint : ∀ p q → ¬ (p ≡ q) → p ∼ q → q ∼ p → ⊥
```