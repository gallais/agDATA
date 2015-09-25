module Data.Number.Digits where

open import Size
open import Data.Nat          as ℕ using (ℕ)
open import Data.Fin          as F using (Fin)
open import Data.Number.Digit as D using (Digit)
open import Data.Product
open import Data.List
open import Data.Sized.Stream as S
open import Data.Sized.Stream.Sequence
open import Function
open import Relation.Binary.PropositionalEquality

Digits : (r : ℕ) → Set
Digits = List ∘ Digit

toℕ : {r : ℕ} (d : Digits r) → ℕ
toℕ {r} = sum ∘ zipWithʳ (λ r^n → (ℕ._* r^n) ∘ F.toℕ ∘ D.getDigit) (powers r)

shiftLeft : {r : ℕ} (d : Digits (ℕ.suc r)) → Digits (ℕ.suc r)
shiftLeft = Digit.[ F.zero ] ∷_

shiftLeft-toℕ : {r : ℕ} (d : Digits (ℕ.suc r)) → toℕ (shiftLeft d) ≡ ℕ.suc r ℕ.* toℕ d
shiftLeft-toℕ d = {!!}
