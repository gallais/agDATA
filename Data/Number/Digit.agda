module Data.Number.Digit where

open import Data.Nat        as ℕ  using (ℕ)
open import Data.Fin        as F  using (Fin)
open import Data.Number.Fin as NF using ()

open import Data.Bool
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

infix 10 [_]
data Digit : (r : ℕ) → Set where
  [_] : {r : ℕ} (k : Fin $ ℕ.suc r) → Digit (ℕ.suc r)

getDigit : {r : ℕ} (d : Digit r) → Fin r
getDigit [ k ] = k

toℕ : {r : ℕ} (d : Digit r) → ℕ
toℕ [ k ] = F.toℕ k

toℕ′ : {r : ℕ} (bd : Bool × Digit r) → ℕ
toℕ′ (b , [ k ]) = NF.toℕ′ (b , k)

suc : {r : ℕ} (d : Digit r) → Bool × Digit r
suc [ k ] = let (b , l) = NF.suc k in b , [ l ]

suc-toℕ : {r : ℕ} (d : Digit r) → toℕ′ (suc d) ≡ ℕ.suc (toℕ d)
suc-toℕ [ k ] = NF.suc-toℕ k

infix 5 _+_
_+_ : {r : ℕ} (d e : Digit r) → Bool × Digit r
[ k ] + [ l ] = let (b , f) = k NF.+ l in (b , [ f ])

_+_-toℕ : {r : ℕ} (d e : Digit r) → toℕ′ (d + e) ≡ toℕ d ℕ.+ toℕ e
_+_-toℕ [ k ] [ l ] = NF._+_-toℕ k l
