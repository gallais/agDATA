module Data.Number.Bool where

open import Data.Bool
open import Data.Nat as ℕ using (ℕ)
open import Data.Product
open import Relation.Binary.PropositionalEquality

pattern #0 = false
pattern #1 = true

toℕ : (c : Bool) → ℕ
toℕ c = if c then 1 else 0

toℕ′ : Bool × Bool → ℕ
toℕ′ (b , c) = 2 ℕ.* toℕ b ℕ.+ toℕ c

_+_ : (b c : Bool) → Bool × Bool
b + c = b ∧ c , b xor c

_+_-toℕ : (b c : Bool) → toℕ b ℕ.+ toℕ c ≡ toℕ′ (b + c)
#0 + #0 -toℕ = refl
#0 + #1 -toℕ = refl
#1 + #0 -toℕ = refl
#1 + #1 -toℕ = refl

