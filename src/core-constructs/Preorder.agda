module core-constructs.Preorder where

record IsPreorder {A : Set} (_≤_ : A → A → Set) : Set where
  field
    reflexive  : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

record Preorder : Set₁ where
  field
    Carrier    : Set
    _≤_        : Carrier → Carrier → Set
    isPreorder : IsPreorder _≤_

  open IsPreorder isPreorder public

  -- Equational reasoning for preorders
  module ≤-Reasoning where
    infix  3 _∎
    infixr 2 _≤⟨_⟩_
    infix  1 begin_

    begin_ : ∀ {x y} → x ≤ y → x ≤ y
    begin p = p

    _≤⟨_⟩_ : ∀ x {y z} → x ≤ y → y ≤ z → x ≤ z
    x ≤⟨ p ⟩ q = transitive p q

    _∎ : ∀ x → x ≤ x
    x ∎ = reflexive

-- Monotonic functions (order-preserving)
Monotonic : {A B : Set} → (_≤₁_ : A → A → Set) → (_≤₂_ : B → B → Set) → (A → B) → Set
Monotonic _≤₁_ _≤₂_ f = ∀ {x y} → x ≤₁ y → f x ≤₂ f y

-- Monotonic function between preorders
_⇒_ : Preorder → Preorder → Set
P ⇒ Q = let open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
            open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)
        in Σ (A → B) λ f → Monotonic _≤₁_ _≤₂_ f
  where open import Data.Product

-- Galois connection between preorders
record GaloisConnection (P Q : Preorder) : Set where
  open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)

  field
    f : A → B  -- Lower adjoint (left adjoint)
    g : B → A  -- Upper adjoint (right adjoint)

    -- Adjunction property: f(x) ≤₂ y  ⟺  x ≤₁ g(y)
    f-g : ∀ {x y} → f x ≤₂ y → x ≤₁ g y
    g-f : ∀ {x y} → x ≤₁ g y → f x ≤₂ y

  -- Derived properties
  f-monotonic : Monotonic _≤₁_ _≤₂_ f
  f-monotonic x≤y = g-f (Preorder.transitive P x≤y (f-g (Preorder.reflexive Q)))

  g-monotonic : Monotonic _≤₂_ _≤₁_ g
  g-monotonic y≤z = f-g (Preorder.transitive Q (g-f (Preorder.reflexive P)) y≤z)

module MeetJoin where

  open import Data.Product
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
