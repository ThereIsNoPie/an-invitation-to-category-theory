---
layout: agda
title: "Meet and Join"
section: "Definitions"
chapter: 1
number: 76
subsections:
  - name: "Preserves Meets/Joins"
    chapter: 1
    number: 87
    anchor: "PreservesMeetsJoins"
  - name: "Generative Effect"
    chapter: 1
    number: 88
    anchor: "GenerativeEffect"
---

# Meet and Join

**Definition 1.76.** Let (P, ≤) be a preorder, and let A ⊆ P be a subset. We say that an element p ∈ P is a *meet of A* if

(a) for all a ∈ A, we have p ≤ a,

(b) for all q such that q ≤ a for all a ∈ A, we have that q ≤ p.

We write p = ⋀ A, p = ⋀_{a∈A} a, or, if the dummy variable a is clear from context, just p = ⋀_A a. If A just consists of two elements, say A = {a, b}, we can denote ⋀ A simply by a ∧ b.

Similarly, we say that p is a *join of A* if

(a) for all a ∈ A we have a ≤ p,

(b) for all q such that a ≤ q for all a ∈ A, we have that p ≤ q.

We write p = ⋁ A or p = ⋁_{a∈A} a, or when A = {a, b} we may simply write p = a ∨ b.

```agda
module definitions.MeetJoin where

open import Data.Product using (_×_)

Subset : Set → Set₁
Subset A = A → Set

-- Lower bound for a subset
-- (a) for all a ∈ A, we have p ≤ a
IsLowerBound : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsLowerBound _≤_ x P = ∀ {y} → P y → x ≤ y

-- Upper bound for a subset
-- (a) for all a ∈ A we have a ≤ p
IsUpperBound : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsUpperBound _≤_ x P = ∀ {y} → P y → y ≤ x

-- Meet (infimum/greatest lower bound)
-- p = ⋀ A
IsMeet : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsMeet _≤_ m P = IsLowerBound _≤_ m P × (∀ {x} → IsLowerBound _≤_ x P → x ≤ m)

-- Join (supremum/least upper bound)
-- p = ⋁ A
IsJoin : {A : Set} → (_≤_ : A → A → Set) → A → Subset A → Set
IsJoin _≤_ j P = IsUpperBound _≤_ j P × (∀ {x} → IsUpperBound _≤_ x P → j ≤ x)

-- Binary meet notation: a ∧ b
_∧_ : {A : Set} → (_≤_ : A → A → Set) → A → A → A → Set
(_≤_ ∧ a) b m = IsMeet _≤_ m (λ x → (x ≡ a) ⊎ (x ≡ b))
  where
    open import Data.Sum using (_⊎_)
    open import Relation.Binary.PropositionalEquality using (_≡_)

-- Binary join notation: a ∨ b
_∨_ : {A : Set} → (_≤_ : A → A → Set) → A → A → A → Set
(_≤_ ∨ a) b j = IsJoin _≤_ j (λ x → (x ≡ a) ⊎ (x ≡ b))
  where
    open import Data.Sum using (_⊎_)
    open import Relation.Binary.PropositionalEquality using (_≡_)

-- Notation for meet of a subset: ⋀ A
⋀ : {A : Set} → (_≤_ : A → A → Set) → Subset A → A → Set
⋀ _≤_ P m = IsMeet _≤_ m P

-- Notation for join of a subset: ⋁ A
⋁ : {A : Set} → (_≤_ : A → A → Set) → Subset A → A → Set
⋁ _≤_ P j = IsJoin _≤_ j P
```

## Definition 1.87: Preserves Meets and Joins {#PreservesMeetsJoins}

**Definition 1.87.** We say that a monotone map f : P → Q *preserves meets* if f(a ∧ b) ≅ f(a) ∧ f(b) for all a, b ∈ P. We similarly say f *preserves joins* if f(a ∨ b) ≅ f(a) ∨ f(b) for all a, b ∈ P.

```agda
open import definitions.Preorder as DP using (Preorder)
open import definitions.MonotoneMap using (_⇒_)
open import Data.Product using (proj₁; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module PreservesMeetsJoins where
  -- A monotone map f : P → Q preserves meets if
  -- f(a ∧ b) ≅ f(a) ∧ f(b) for all a, b ∈ P
  PreservesMeets : (P Q : Preorder) → (P ⇒ Q) → Set
  PreservesMeets P Q f-mono =
    let open DP.Preorder P renaming (Carrier to A; _≤_ to _≤P_)
        open DP.Preorder Q renaming (Carrier to B; _≤_ to _≤Q_; _≅_ to _≅Q_)
        f = proj₁ f-mono
    in ∀ (a b m : A) → IsMeet _≤P_ m (λ x → (x ≡ a) ⊎ (x ≡ b)) →
       ∀ (n : B) → IsMeet _≤Q_ n (λ y → (y ≡ f a) ⊎ (y ≡ f b)) →
       f m ≅Q n

  -- A monotone map f : P → Q preserves joins if
  -- f(a ∨ b) ≅ f(a) ∨ f(b) for all a, b ∈ P
  PreservesJoins : (P Q : Preorder) → (P ⇒ Q) → Set
  PreservesJoins P Q f-mono =
    let open DP.Preorder P renaming (Carrier to A; _≤_ to _≤P_)
        open DP.Preorder Q renaming (Carrier to B; _≤_ to _≤Q_; _≅_ to _≅Q_)
        f = proj₁ f-mono
    in ∀ (a b j : A) → IsJoin _≤P_ j (λ x → (x ≡ a) ⊎ (x ≡ b)) →
       ∀ (k : B) → IsJoin _≤Q_ k (λ y → (y ≡ f a) ⊎ (y ≡ f b)) →
       f j ≅Q k
```

## Definition 1.88: Generative Effect {#GenerativeEffect}

**Definition 1.88.** We say that a monotone map f : P → Q has a *generative effect* if there exist elements a, b ∈ P such that

f(a) ∨ f(b) ≠ f(a ∨ b).

```agda
module GenerativeEffect where
  open import Relation.Nullary using (¬_)

  -- A monotone map f : P → Q has a generative effect if
  -- there exist a, b ∈ P such that f(a) ∨ f(b) ≠ f(a ∨ b)
  HasGenerativeEffect : (P Q : Preorder) → (P ⇒ Q) → Set
  HasGenerativeEffect P Q f-mono =
    let open DP.Preorder P renaming (Carrier to A; _≤_ to _≤P_)
        open DP.Preorder Q renaming (Carrier to B; _≤_ to _≤Q_)
        f = proj₁ f-mono
    in Σ[ a ∈ A ] Σ[ b ∈ A ] Σ[ j ∈ A ] Σ[ k ∈ B ]
       (IsJoin _≤P_ j (λ x → (x ≡ a) ⊎ (x ≡ b)) ×
        IsJoin _≤Q_ k (λ y → (y ≡ f a) ⊎ (y ≡ f b)) ×
        ¬ (f j ≡ k))
```
