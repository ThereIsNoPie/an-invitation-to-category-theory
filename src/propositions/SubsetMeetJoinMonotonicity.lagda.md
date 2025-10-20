---
layout: agda
title: "Subset Meet and Join Monotonicity"
section: "Propositions"
chapter: 1
number: 86
---

# Subset Meet and Join Monotonicity

## Textbook Definition

**Proposition 1.86.** Suppose (P, ≤) is a preorder and A ⊆ B ⊆ P are subsets that have meets. Then ∧ B ≤ ∧ A.

Similarly, if A and B have joins, then ∨ A ≤ ∨ B.

## Agda Setup

```agda
module propositions.SubsetMeetJoinMonotonicity where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import definitions.Preorder using (Preorder)
open import definitions.MeetJoin using (Subset; IsMeet; IsJoin; IsLowerBound; IsUpperBound)
```

## Proposition

```agda
meet-subset-antitone : (P : Preorder)
                     → (A B : Subset (Preorder.Carrier P))
                     → (A⊆B : ∀ {x} → A x → B x)
                     → (m : Preorder.Carrier P) → IsMeet (Preorder._≤_ P) m A
                     → (n : Preorder.Carrier P) → IsMeet (Preorder._≤_ P) n B
                     → Preorder._≤_ P n m

join-subset-monotone : (P : Preorder)
                     → (A B : Subset (Preorder.Carrier P))
                     → (A⊆B : ∀ {x} → A x → B x)
                     → (j : Preorder.Carrier P) → IsJoin (Preorder._≤_ P) j A
                     → (k : Preorder.Carrier P) → IsJoin (Preorder._≤_ P) k B
                     → Preorder._≤_ P j k
```

## Proof: Part 1 (Meets are Antitone in Subset Inclusion)

If A ⊆ B and both have meets, then ∧ B ≤ ∧ A.

**Strategy:** Let m = ∧ A and n = ∧ B. For any a ∈ A we also have a ∈ B (since A ⊆ B), so n ≤ a because n is a lower bound for B. Thus n is also a lower bound for A, and hence n ≤ m because m is A's greatest lower bound.

```agda
meet-subset-antitone P A B A⊆B m (m-lb , m-glb) n (n-lb , n-glb) = n≤m
  where
    open Preorder P

    -- n is a lower bound for B, so for any a ∈ A, we have a ∈ B (by A⊆B)
    -- and therefore n ≤ a
    n-lb-A : IsLowerBound _≤_ n A
    n-lb-A {a} a∈A = n-lb (A⊆B a∈A)

    -- Since n is a lower bound for A and m is the greatest lower bound for A,
    -- we have n ≤ m
    n≤m : n ≤ m
    n≤m = m-glb n-lb-A
```

## Proof: Part 2 (Joins are Monotone in Subset Inclusion)

If A ⊆ B and both have joins, then ∨ A ≤ ∨ B.

**Strategy:** Let j = ∨ A and k = ∨ B. For any a ∈ A we also have a ∈ B (since A ⊆ B), so a ≤ k because k is an upper bound for B. Thus k is also an upper bound for A, and hence j ≤ k because j is A's least upper bound.

```agda
join-subset-monotone P A B A⊆B j (j-ub , j-lub) k (k-ub , k-lub) = j≤k
  where
    open Preorder P

    -- k is an upper bound for B, so for any a ∈ A, we have a ∈ B (by A⊆B)
    -- and therefore a ≤ k
    k-ub-A : IsUpperBound _≤_ k A
    k-ub-A {a} a∈A = k-ub (A⊆B a∈A)

    -- Since k is an upper bound for A and j is the least upper bound for A,
    -- we have j ≤ k
    j≤k : j ≤ k
    j≤k = j-lub k-ub-A
```
