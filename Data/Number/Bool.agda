module Data.Number.Bool where

open import Data.Bool
open import Data.Nat as ℕ using (ℕ)
open import Data.Product
open import Relation.Binary.PropositionalEquality

toℕ : (c : Bool) → ℕ
toℕ c = if c then 1 else 0

toℕ′ : Bool × Bool → ℕ
toℕ′ (b , c) = 2 ℕ.* toℕ b ℕ.+ toℕ c

_+_ : (b c : Bool) → Bool × Bool
b + c = b ∧ c , b xor c

_+_-toℕ : (b c : Bool) → toℕ b ℕ.+ toℕ c ≡ toℕ′ (b + c)
_+_-toℕ true  true  = refl
_+_-toℕ true  false = refl
_+_-toℕ false true  = refl
_+_-toℕ false false = refl

