module Data.Number.Nat where

open import Data.Nat

infixl 8 _^_

_^_ : (r k : ℕ) → ℕ
r ^ zero  = 1
r ^ suc k = r * r ^ k
