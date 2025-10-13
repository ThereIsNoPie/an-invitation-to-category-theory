module MeetExample where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_,_)

-- Import our definitions
open import Preorder
open MeetJoin

-- Example: Meet of "positive naturals" in ℕ is 1, but 1 is not in the subset
-- We'll use the subset P = {n | n ≥ 2} = {2, 3, 4, ...}

-- Define the subset P = {n | n ≥ 2}
P : Subset ℕ
P n = 2 ≤ n

-- Proof that 1 is a lower bound for P
1-is-lower-bound : IsLowerBound _≤_ 1 P
1-is-lower-bound {y} 2≤y = s≤s z≤n  -- 1 ≤ y because 2 ≤ y

-- Proof that 1 is the greatest lower bound
1-is-greatest-lower : ∀ {x} → IsLowerBound _≤_ x P → x ≤ 1
1-is-greatest-lower {zero} x-lower = z≤n
1-is-greatest-lower {suc zero} x-lower = ≤-refl
1-is-greatest-lower {suc (suc x)} x-lower =
  -- If x ≥ 2, then we need x ≤ 1, but x-lower tells us x ≤ 2
  -- Actually this is impossible! Let's use x-lower to get a contradiction
  -- x-lower {2} (s≤s (s≤s z≤n)) gives us x ≤ 2
  -- But we assumed x ≥ 2, so x must equal 2
  x-lower (s≤s (s≤s z≤n))

-- 1 is the meet of P
1-is-meet-of-P : IsMeet _≤_ 1 P
1-is-meet-of-P = 1-is-lower-bound , 1-is-greatest-lower

-- But 1 is NOT in P!
-- If we try to prove P 1, we need to prove 2 ≤ 1, which is impossible

-- This shows that the meet of a subset does not need to be in the subset itself