---
layout: agda
title: "Preorder Bool-Category Correspondence"
section: "Propositions"
chapter: 2
number: 32
---

# Preorder Bool-Category Correspondence

## Textbook Definition

**Theorem 2.32.** There is a one-to-one correspondence between preorders and Bool-categories.

**Proof.** Let's check that we can construct a preorder from any Bool-category. Since B = {false, true}, Definition 2.30 says a Bool-category consists of two things:

(i) a set Ob(X),

(ii) for every x, y ∈ Ob(X) an element X(x, y) ∈ B, i.e. the element X(x, y) is either true or false.

We will use these two things to begin forming a preorder whose elements are the objects of X. So let's call the preorder (X, ≤), and let X := Ob(X). For the ≤ relation, let's declare x ≤ y iff X(x, y) = true. We have the makings of a preorder, but for it to work, the ≤ relation must be reflexive and transitive. Let's see if we get these from the properties guaranteed by Definition 2.30:

(a) for every element x ∈ X we have true ≤ X(x, x),

(b) for every three elements x, y, z ∈ X we have X(x, y) ∧ X(y, z) ≤ X(x, z).

For b ∈ Bool, if true ≤ b then b = true, so the first statement says X(x, x) = true, which means x ≤ x. For the second statement, one can consult Eq. (2.16). Since false ≤ b for all b ∈ B, the only way statement (b) has any force is if X(x, y) = true and X(y, z) = true, in which case it forces X(x, z) = true. This condition exactly translates as saying that x ≤ y and y ≤ z implies x ≤ z. Thus we have obtained reflexivity and transitivity from the two axioms of Bool-categories.

## Agda Setup

```agda
module propositions.chapter2.PreorderBoolCategoryCorrespondence where

open import definitions.chapter1.Preorder using (Preorder; IsPreorder)
open import definitions.chapter2.SymmetricMonoidalPreorder
  using (SymmetricMonoidalStructure; SymmetricMonoidalPreorder)
open import definitions.chapter2.VCategory using (VCategory)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂; trans)
```

## The Bool Symmetric Monoidal Preorder

We first define Bool as a symmetric monoidal preorder with ordering false ≤ true, monoidal unit true, and monoidal product ∧.

```agda
-- The ordering on Bool: false ≤ true
data _≤Bool_ : Bool → Bool → Set where
  false≤false : false ≤Bool false
  false≤true  : false ≤Bool true
  true≤true   : true ≤Bool true

-- Bool is a preorder
≤Bool-refl : ∀ {x : Bool} → x ≤Bool x
≤Bool-trans : ∀ {x y z : Bool} → x ≤Bool y → y ≤Bool z → x ≤Bool z
Bool-preorder : Preorder

-- ∧ satisfies the monoidal structure conditions
∧-monotonic : ∀ {x₁ x₂ y₁ y₂ : Bool} → x₁ ≤Bool y₁ → x₂ ≤Bool y₂ → (x₁ ∧ x₂) ≤Bool (y₁ ∧ y₂)
∧-identityˡ : ∀ {x : Bool} → true ∧ x ≡ x
∧-identityʳ : ∀ {x : Bool} → x ∧ true ≡ x
∧-assoc : ∀ (x y z : Bool) → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
∧-comm : ∀ (x y : Bool) → x ∧ y ≡ y ∧ x

Bool-monoidal-structure : SymmetricMonoidalStructure Bool-preorder
Bool-monoidal : SymmetricMonoidalPreorder
```

## Implementation: Bool as Symmetric Monoidal Preorder

```agda
≤Bool-refl {false} = false≤false
≤Bool-refl {true} = true≤true

≤Bool-trans false≤false false≤false = false≤false
≤Bool-trans false≤false false≤true = false≤true
≤Bool-trans false≤true true≤true = false≤true
≤Bool-trans true≤true true≤true = true≤true

Bool-preorder = record
  { Carrier = Bool
  ; _≤_ = _≤Bool_
  ; isPreorder = record
      { reflexive = ≤Bool-refl
      ; transitive = ≤Bool-trans
      }
  }

∧-monotonic false≤false false≤false = false≤false
∧-monotonic false≤false false≤true = false≤false
∧-monotonic false≤false true≤true = false≤false
∧-monotonic false≤true false≤false = false≤false
∧-monotonic false≤true false≤true = false≤true
∧-monotonic false≤true true≤true = false≤true
∧-monotonic true≤true false≤false = false≤false
∧-monotonic true≤true false≤true = false≤true
∧-monotonic true≤true true≤true = true≤true

∧-identityˡ {false} = refl
∧-identityˡ {true} = refl

∧-identityʳ {false} = refl
∧-identityʳ {true} = refl

∧-assoc false y z = refl
∧-assoc true y z = refl

∧-comm false false = refl
∧-comm false true = refl
∧-comm true false = refl
∧-comm true true = refl

Bool-monoidal-structure = record
  { I = true
  ; _⊗_ = _∧_
  ; monotonicity = ∧-monotonic
  ; left-unit = ∧-identityˡ
  ; right-unit = ∧-identityʳ
  ; associativity = λ {x} {y} {z} → ∧-assoc x y z
  ; symmetry = λ {x} {y} → ∧-comm x y
  }

Bool-monoidal = record
  { preorder = Bool-preorder
  ; structure = Bool-monoidal-structure
  }
```

## Helper Lemma: true ≤Bool b implies b ≡ true

This key lemma is used to show reflexivity.

```agda
true≤-implies-true : ∀ {b : Bool} → true ≤Bool b → b ≡ true
true≤-implies-true true≤true = refl
```

## Proposition: Part 1 Bool-Category to Preorder

From any Bool-category X, we can construct a preorder by taking:
- Elements: Ob(X)
- Order: x ≤ y iff X(x, y) = true

```agda
BoolCategory→Preorder : VCategory Bool-monoidal → Preorder
```

### Proof: Part 1 Bool-Category to Preorder

**Strategy:** We construct the preorder with carrier Ob(X) and order defined by X(x, y) = true. Reflexivity follows from the identity axiom I ≤ X(x, x) where I = true. Transitivity follows from the composition axiom X(x, y) ∧ X(y, z) ≤ X(x, z).

```agda
BoolCategory→Preorder X = record
  { Carrier = Ob
  ; _≤_ = λ x y → hom x y ≡ true
  ; isPreorder = record
      { reflexive = reflexive-proof
      ; transitive = transitive-proof
      }
  }
  where
    open VCategory X

    -- Reflexivity: X(x, x) = true for all x
    -- Proof: From identity axiom, true ≤Bool X(x, x)
    -- Since true ≤Bool b implies b = true, we have X(x, x) = true
    reflexive-proof : ∀ {x} → hom x x ≡ true
    reflexive-proof {x} = true≤-implies-true identity

    -- Transitivity: if X(x, y) = true and X(y, z) = true, then X(x, z) = true
    -- Proof: From composition axiom, X(x, y) ∧ X(y, z) ≤Bool X(x, z)
    -- If X(x, y) = true and X(y, z) = true, then true ∧ true ≤Bool X(x, z)
    -- So true ≤Bool X(x, z), which implies X(x, z) = true
    transitive-proof : ∀ {x y z} → hom x y ≡ true → hom y z ≡ true → hom x z ≡ true
    transitive-proof {x} {y} {z} xy≡true yz≡true =
      true≤-implies-true (subst (λ b → b ≤Bool hom x z) eq-∧ composition)
      where
        -- hom x y ∧ hom y z ≡ true ∧ true ≡ true
        eq-∧ : (hom x y ∧ hom y z) ≡ true
        eq-∧ = trans (cong₂ _∧_ xy≡true yz≡true) refl
```

## Proposition: Part 2 Preorder to Bool-Category

From any preorder (P, ≤), we can construct a Bool-category. However, this requires decidability of the order relation ≤. We state this as a type signature to show the correspondence exists.

```agda
-- To construct a Bool-category from a preorder, we need a way to decide
-- whether x ≤ y holds. We represent this as a record type.
record PreorderWithDecidableOrder : Set₁ where
  field
    preorder : Preorder

  open Preorder preorder public

  field
    -- A function that returns true iff x ≤ y
    decide-≤ : Carrier → Carrier → Bool
    -- If decide-≤ returns true, then x ≤ y holds
    decide-≤-sound : ∀ {x y} → decide-≤ x y ≡ true → x ≤ y
    -- If x ≤ y holds, then decide-≤ returns true
    decide-≤-complete : ∀ {x y} → x ≤ y → decide-≤ x y ≡ true

Preorder→BoolCategory : PreorderWithDecidableOrder → VCategory Bool-monoidal
```

### Proof: Part 2 Preorder to Bool-Category

**Strategy:** We define the hom-object function using the decidability predicate. The identity axiom follows from reflexivity of ≤. The composition axiom follows from transitivity of ≤.

```agda
Preorder→BoolCategory P = record
  { Ob = Carrier
  ; hom = λ x y → decide-≤ x y
  ; identity = identity-proof
  ; composition = composition-proof
  }
  where
    open PreorderWithDecidableOrder P

    -- Identity: true ≤Bool hom x x
    -- Since x ≤ x (reflexivity), decide-≤ x x = true
    identity-proof : ∀ {x} → true ≤Bool decide-≤ x x
    identity-proof {x} with decide-≤ x x in eq
    ... | false = ⊥-elim (false≢true (trans (sym (decide-≤-complete reflexive)) eq))
      where
        false≢true : true ≡ false → ⊥
        false≢true ()
    ... | true = true≤true

    -- Helper: false ≤Bool any value
    false≤-any : ∀ {b : Bool} → false ≤Bool b
    false≤-any {false} = false≤false
    false≤-any {true} = false≤true

    -- Composition: hom x y ∧ hom y z ≤Bool hom x z
    -- If x ≤ y and y ≤ z, then x ≤ z (transitivity), so all three hom are true
    -- Otherwise, false ≤Bool _ always holds
    composition-proof : ∀ {x y z} → (decide-≤ x y ∧ decide-≤ y z) ≤Bool decide-≤ x z
    composition-proof {x} {y} {z} with decide-≤ x y in xy-eq | decide-≤ y z in yz-eq
    ... | false | false = false≤-any
    ... | false | true = false≤-any
    ... | true | false = false≤-any
    ... | true | true with decide-≤ x z in xz-eq
    ...   | false = ⊥-elim (false≢true (trans (sym (decide-≤-complete (transitive (decide-≤-sound xy-eq) (decide-≤-sound yz-eq)))) xz-eq))
      where
        false≢true : true ≡ false → ⊥
        false≢true ()
    ...   | true = true≤true
```

## Proposition: Part 3 The Roundtrip Proofs

To show this is a true one-to-one correspondence, we need to prove that these functions are inverses of each other.

```agda
-- Roundtrip 1: Bool-category → Preorder → Bool-category
-- The resulting Bool-category has the same objects and hom-objects as the original
roundtrip-BoolCat : (X : VCategory Bool-monoidal) →
                    (x y : VCategory.Ob X) →
                    VCategory.hom (Preorder→BoolCategory
                      (record
                        { preorder = BoolCategory→Preorder X
                        ; decide-≤ = λ x y → VCategory.hom X x y
                        ; decide-≤-sound = λ {x} {y} eq → eq
                        ; decide-≤-complete = λ {x} {y} prf → prf
                        })) x y
                    ≡ VCategory.hom X x y

-- Roundtrip 2: Preorder → Bool-category → Preorder
-- The resulting preorder has the same carrier and order relation as the original
roundtrip-Preorder : (P : PreorderWithDecidableOrder) →
                     (x y : Preorder.Carrier (PreorderWithDecidableOrder.preorder P)) →
                     let open Preorder (PreorderWithDecidableOrder.preorder P) in
                     (x ≤ y → Preorder._≤_ (BoolCategory→Preorder (Preorder→BoolCategory P)) x y) ×
                     (Preorder._≤_ (BoolCategory→Preorder (Preorder→BoolCategory P)) x y → x ≤ y)
```

## Proof: Part 3 Roundtrip 1 (Bool-category → Preorder → Bool-category)

**Strategy:** When we convert a Bool-category X to a preorder and back, the hom-objects are preserved because:
1. Converting to preorder defines `x ≤ y` as `X(x,y) = true`
2. Converting back defines `hom(x,y) = true` iff `x ≤ y`
3. Therefore `hom(x,y) = X(x,y)`

```agda
roundtrip-BoolCat X x y = refl
```

## Proof: Part 3 Roundtrip 2 (Preorder → Bool-category → Preorder)

**Strategy:** When we convert a decidable preorder P to a Bool-category and back, the order relation is preserved because:
1. Converting to Bool-category defines `X(x,y) = true` iff `x ≤ y`
2. Converting back defines `x ≤' y` as `X(x,y) = true`
3. Therefore `x ≤' y` iff `x ≤ y`

```agda
roundtrip-Preorder P x y = (forward , backward)
  where
    open PreorderWithDecidableOrder P

    -- If x ≤ y in the original preorder, then x ≤ y in the roundtrip preorder
    forward : x ≤ y → Preorder._≤_ (BoolCategory→Preorder (Preorder→BoolCategory P)) x y
    forward x≤y = decide-≤-complete x≤y

    -- If x ≤ y in the roundtrip preorder, then x ≤ y in the original preorder
    backward : Preorder._≤_ (BoolCategory→Preorder (Preorder→BoolCategory P)) x y → x ≤ y
    backward x≤'y = decide-≤-sound x≤'y
```

## Interpretation

This proposition establishes a **true one-to-one correspondence** (bijection) between preorders and Bool-categories:

- **Bool-categories are preorders:** Every Bool-category has an underlying preorder structure where the order is determined by when hom-objects equal true.

- **Preorders (with decidable order) are Bool-categories:** Every preorder with a decidable order relation can be viewed as enriched in Bool, where "there is a morphism from x to y" (i.e., X(x, y) = true) means precisely "x ≤ y".

- **The correspondence is bijective:** The roundtrip proofs show that:
  - Converting a Bool-category to a preorder and back preserves the hom-objects exactly
  - Converting a preorder to a Bool-category and back preserves the order relation exactly

This demonstrates that enrichment in Bool is **precisely** the same thing as being a preorder. The identity and composition axioms of V-categories correspond exactly to reflexivity and transitivity of preorders, and the two notions are completely interchangeable.
```
