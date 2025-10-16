---
layout: agda
title: "Meet and Join"
section: "Definitions"
chapter: 1
number: 96
---

# Meet and Join

Definitions of meets (infimums) and joins (supremums) for preorders.

```agda
module definitions.MeetJoin where

open import Data.Product using (_×_)
open import Relation.Binary

Subset : Set → Set₁
Subset A = A → Set

-- Lower bound for a subset
IsLowerBound : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsLowerBound _≤_ x P = ∀ {y} → P y → x ≤ y

-- Upper bound for a subset
IsUpperBound : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsUpperBound _≤_ x P = ∀ {y} → P y → y ≤ x

-- Meet (infimum/greatest lower bound)
IsMeet : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsMeet _≤_ m P = IsLowerBound _≤_ m P × (∀ {x} → IsLowerBound _≤_ x P → x ≤ m)

-- Join (supremum/least upper bound)
IsJoin : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsJoin _≤_ j P = IsUpperBound _≤_ j P × (∀ {x} → IsUpperBound _≤_ x P → j ≤ x)
```
