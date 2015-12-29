module Data.Number.Result where

open import Data.Bool

infix 3 _∙_
record _withCarry (A : Set) : Set where
  constructor _∙_
  field
    carry : Bool
    value : A
open _withCarry public

fmap : {A B : Set} (f : A → B) → A withCarry → B withCarry
fmap f r = carry r ∙ f (value r)

