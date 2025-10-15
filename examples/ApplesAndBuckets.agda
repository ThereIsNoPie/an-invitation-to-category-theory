-- Example 1.109: Apples and Buckets
-- This file demonstrates the three adjoint functors induced by a function f : A → B

module ApplesAndBuckets where

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ-syntax; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; _⊔_)

-- Powerset as a type: A subset of X is represented as X → Set
Powerset : Set → Set₁
Powerset X = X → Set

-- Subset inclusion
_⊆_ : {X : Set} → Powerset X → Powerset X → Set
_⊆_ S T = ∀ {x} → S x → T x

module ApplesAndBucketsTheorem (Apples Buckets : Set) (f : Apples → Buckets) where

  A = Apples
  B = Buckets

  𝒫A = Powerset A
  𝒫B = Powerset B

  -- f* : P(B) → P(A)
  -- Pullback/Preimage: given buckets, return apples they contain
  -- f*(B') = { a ∈ A | f(a) ∈ B' }
  f* : 𝒫B → 𝒫A
  f* B' a = B' (f a)

  -- f! : P(A) → P(B)
  -- Direct image (existential): given apples, return buckets containing at least one
  -- f!(A') = { b ∈ B | ∃a ∈ A'. f(a) = b }
  f! : 𝒫A → 𝒫B
  f! A' b = Σ[ a ∈ A ] (A' a × f a ≡ b)

  -- f∗ : P(A) → P(B)
  -- Universal image: given apples, return buckets where ALL apples are from the subset
  -- f∗(A') = { b ∈ B | ∀a. f(a) = b → a ∈ A' }
  f∗ : 𝒫A → 𝒫B
  f∗ A' b = ∀ {a} → f a ≡ b → A' a

  -- Adjunction 1: f! ⊣ f*
  -- For all A' ⊆ A and B' ⊆ B: f!(A') ⊆ B' ⟺ A' ⊆ f*(B')

  -- If f!(A') ⊆ B', then A' ⊆ f*(B')
  -- "If all buckets containing an apple from A' are in B',
  --  then all apples in A' map to buckets in B'"
  f!⊆→⊆f* : ∀ {A' B'} → f! A' ⊆ B' → A' ⊆ f* B'
  f!⊆→⊆f* f!A'⊆B' {a} a∈A' = f!A'⊆B' (a , a∈A' , refl)

  -- If A' ⊆ f*(B'), then f!(A') ⊆ B'
  -- "If all apples in A' map to buckets in B',
  --  then all buckets containing an apple from A' are in B'"
  ⊆f*→f!⊆ : ∀ {A' B'} → A' ⊆ f* B' → f! A' ⊆ B'
  ⊆f*→f!⊆ A'⊆f*B' {b} (a , a∈A' , refl) = A'⊆f*B' a∈A'

  -- Adjunction 2: f* ⊣ f∗
  -- For all B' ⊆ B and A' ⊆ A: f*(B') ⊆ A' ⟺ B' ⊆ f∗(A')

  -- If f*(B') ⊆ A', then B' ⊆ f∗(A')
  -- "If all apples in buckets B' are in A',
  --  then all buckets B' are all-A' (all their apples are from A')"
  f*⊆→⊆f∗ : ∀ {B' A'} → f* B' ⊆ A' → B' ⊆ f∗ A'
  f*⊆→⊆f∗ f*B'⊆A' {b} b∈B' {a} refl = f*B'⊆A' b∈B'

  -- If B' ⊆ f∗(A'), then f*(B') ⊆ A'
  -- "If all buckets in B' are all-A' (all their apples are from A'),
  --  then all apples in buckets B' are in A'"
  ⊆f∗→f*⊆ : ∀ {B' A'} → B' ⊆ f∗ A' → f* B' ⊆ A'
  ⊆f∗→f*⊆ B'⊆f∗A' {a} fa∈B' = B'⊆f∗A' fa∈B' refl

-- Example instantiation: Apples and Buckets with concrete types
module ConcreteExample where

  data Apple : Set where
    apple1 apple2 apple3 : Apple

  data Bucket : Set where
    bucket1 bucket2 : Bucket

  -- Each apple goes in a bucket
  placement : Apple → Bucket
  placement apple1 = bucket1
  placement apple2 = bucket1
  placement apple3 = bucket2

  open ApplesAndBucketsTheorem Apple Bucket placement

  -- Example: subset of apples
  AppleSubset : Powerset Apple
  AppleSubset apple1 = ⊤ where
    data ⊤ : Set where
      tt : ⊤
  AppleSubset apple2 = ⊥
  AppleSubset apple3 = ⊥

  -- f!(AppleSubset) = buckets containing at least one of {apple1}
  -- = {bucket1} because apple1 is in bucket1

  -- f∗(AppleSubset) = buckets where ALL apples are from {apple1}
  -- = ∅ because bucket1 has apple2 which is not in AppleSubset
  --   and bucket2 has apple3 which is not in AppleSubset
