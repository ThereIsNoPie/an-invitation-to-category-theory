module MeetExample where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_,_)
open import Data.Empty using (⊥; ⊥-elim)

-- Import our definitions
open import Preorder
open MeetJoin

-- Example: Meet of "positive naturals" in ℕ is 1, but 1 is not in the subset
-- We'll use the subset P = {n | n ≥ 2} = {2, 3, 4, ...}

-- Define the subset P = {n | n ≥ 2}
P : Subset ℕ
P n = 2 ≤ n

-- Helper: 2 ≤ 1 is impossible
2≰1 : 2 ≤ 1 → ⊥
2≰1 (s≤s ())

-- Proof that 2 is a lower bound for P
2-is-lower-bound : IsLowerBound _≤_ 2 P
2-is-lower-bound 2≤y = 2≤y  -- 2 ≤ 2 and 2 ≤ y, so 2 ≤ y

-- NOTE: This proof has issues - mathematically, 2 is also a lower bound for P,
-- and 2 is the greatest lower bound, not 1. This example may need revision.
-- Proof that 2 is the greatest lower bound
2-is-greatest-lower : ∀ {x} → IsLowerBound _≤_ x P → x ≤ 2
2-is-greatest-lower {x} x-is-lower =  x-is-lower (s≤s (s≤s z≤n))

-- -- -- 2 is the meet of P
2-is-meet-of-P : IsMeet _≤_ 2 P
2-is-meet-of-P = 2-is-lower-bound , 2-is-greatest-lower

-- But 2 is NOT in P!
-- If we try to prove P 2, we need to prove 2 ≤ 2, which is impossible

-- This shows that the meet of a subset does not need to be in the subset itself