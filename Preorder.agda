module Preorder where

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

-- Proposition 1.101: Equivalence between Galois connection and unit/counit conditions
module GaloisTheorems (P Q : Preorder) where
  open Preorder P renaming (Carrier to A; _≤_ to _≤₁_)
  open Preorder Q renaming (Carrier to B; _≤_ to _≤₂_)

  -- Forward direction: Galois connection implies unit/counit conditions
  module FromGalois (gc : GaloisConnection P Q) where
    open GaloisConnection gc
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- p ≤ g(f(p)) for all p
    unit : ∀ (p : A) → p ≤₁ g (f p)
    unit p = beginP
      p       ≤P⟨ f-g lem ⟩
      g (f p) ∎P
      where
        lem : f p ≤₂ f p
        lem = f p ∎Q

    -- f(g(q)) ≤ q for all q
    counit : ∀ (q : B) → f (g q) ≤₂ q
    counit q = beginQ
      f (g q) ≤Q⟨ g-f lem ⟩
      q       ∎Q
      where
        lem : g q ≤₁ g q
        lem = g q ∎P

  -- Backward direction: unit/counit conditions imply Galois connection
  module ToGalois (f : A → B) (g : B → A)
                  (f-mono : Monotonic _≤₁_ _≤₂_ f)
                  (g-mono : Monotonic _≤₂_ _≤₁_ g)
                  (unit : ∀ (p : A) → p ≤₁ g (f p))
                  (counit : ∀ (q : B) → f (g q) ≤₂ q) where

    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)

    -- f(x) ≤ y → x ≤ g(y)
    f-g-adj : ∀ {x y} → f x ≤₂ y → x ≤₁ g y
    f-g-adj {x} {y} fx≤y = beginP
      x       ≤P⟨ unit x ⟩
      g (f x) ≤P⟨ g-mono fx≤y ⟩
      g y     ∎P

    -- x ≤ g(y) → f(x) ≤ y
    g-f-adj : ∀ {x y} → x ≤₁ g y → f x ≤₂ y
    g-f-adj {x} {y} x≤gy = beginQ
      f x     ≤Q⟨ f-mono x≤gy ⟩
      f (g y) ≤Q⟨ counit y ⟩
      y       ∎Q

    galoisConnection : GaloisConnection P Q
    galoisConnection = record
      { f = f
      ; g = g
      ; f-g = f-g-adj
      ; g-f = g-f-adj
      }

  -- Proposition 1.104: Right adjoints preserve meets, left adjoints preserve joins
  module Prop104 (gc : GaloisConnection P Q) where
    open GaloisConnection gc
    open MeetJoin
    open Preorder.≤-Reasoning P renaming (begin_ to beginP_; _≤⟨_⟩_ to _≤P⟨_⟩_; _∎ to _∎P)
    open Preorder.≤-Reasoning Q renaming (begin_ to beginQ_; _≤⟨_⟩_ to _≤Q⟨_⟩_; _∎ to _∎Q)
    open import Data.Product
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)

    -- Image of a subset under a function
    image : {X Y : Set} → (X → Y) → Subset X → Subset Y
    image h S y = ∃[ x ] (S x × h x ≡ y)

    -- Right adjoints preserve meets: g(∧A) ∼= ∧g(A)
    module RightAdjointPreservesMeet (S : Subset B) (m : B) (meet-S : IsMeet _≤₂_ m S) where

      -- g(m) is a lower bound for g(S)
      g-lower-bound : IsLowerBound _≤₁_ (g m) (image g S)
      g-lower-bound {p} (q , Sq , refl) = beginP
        g m ≤P⟨ g-monotonic (proj₁ meet-S Sq) ⟩
        g q ∎P
        

      -- g(m) is the greatest lower bound for g(S)
      g-greatest-lower : ∀ {x} → IsLowerBound _≤₁_ x (image g S) → x ≤₁ g m
      g-greatest-lower {x} x-lower = beginP
        x     ≤P⟨ f-g lem ⟩
        g m   ∎P
        where
          lem : f x ≤₂ m
          lem = proj₂ meet-S λ {q} Sq → g-f (x-lower (q , Sq , refl))

      g-preserves-meet : IsMeet _≤₁_ (g m) (image g S)
      g-preserves-meet = g-lower-bound , g-greatest-lower

    -- Left adjoints preserve joins: f(∨A) ∼= ∨f(A)
    module LeftAdjointPreserveJoin (S : Subset A) (j : A) (join-S : IsJoin _≤₁_ j S) where

      -- f(j) is an upper bound for f(S)
      f-upper-bound : IsUpperBound _≤₂_ (f j) (image f S)
      f-upper-bound {q} (p , Sp , refl) = beginQ
        f p ≤Q⟨ f-monotonic (proj₁ join-S Sp) ⟩
        f j ∎Q

      -- f(j) is the least upper bound for f(S)
      f-least-upper : ∀ {y} → IsUpperBound _≤₂_ y (image f S) → f j ≤₂ y
      f-least-upper {y} y-upper = beginQ
        f j ≤Q⟨ g-f lem ⟩
        y   ∎Q
        where
          open FromGalois gc
          lem : j ≤₁ g y
          lem = proj₂ join-S λ {p} Sp → beginP
            p       ≤P⟨ unit p ⟩
            g (f p) ≤P⟨ g-monotonic (y-upper (p , Sp , refl)) ⟩
            g y     ∎P

      f-preserves-join : IsJoin _≤₂_ (f j) (image f S)
      f-preserves-join = f-upper-bound , f-least-upper

