module Data.Number.Digit where

open import Data.Nat    as ℕ  using (ℕ)
open import Data.Fin    as F  using (Fin)
import Data.Number.Fin  as NF
import Data.Number.Bool as B

open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning

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

suc-inv : {r : ℕ} (d e : Digit (ℕ.suc r)) (c : Bool) (eq : suc d ≡ (c , e)) →
          if c then e ≡ [ F.zero ] else ⊤
suc-inv _ _ false _ = tt
suc-inv [ k ] [ l ] true eq = cong [_] $ NF.suc-inv k l true $ cong f eq
  where f : {r : ℕ} → Bool × Digit r → Bool × Fin r
        f (b , [ k ]) = b , k

infix 5 _+_
_+_ : {r : ℕ} (d e : Digit r) → Bool × Digit r
[ k ] + [ l ] = let (b , f) = k NF.+ l in (b , [ f ])

_+_-toℕ : {r : ℕ} (d e : Digit r) → toℕ′ (d + e) ≡ toℕ d ℕ.+ toℕ e
_+_-toℕ [ k ] [ l ] = NF._+_-toℕ k l

infix 5 _+_′_
_+_′_ : {r :  ℕ} (d e : Digit r) (c : Bool) → Bool × Digit r
[ k ] + [ l ] ′ c = let (c′ , sk+l) = k NF.+ l ′ c in c′ , [ sk+l ]

_+_′_-toℕ : {n : ℕ} (k l : Digit n) (c : Bool) → toℕ′ (k + l ′ c) ≡ B.toℕ c ℕ.+ toℕ k ℕ.+ toℕ l
_+_′_-toℕ [ k ] [ l ] c = NF._+_′_-toℕ k l c
