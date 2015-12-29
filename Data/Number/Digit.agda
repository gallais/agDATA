module Data.Number.Digit where

open import Data.Nat    as ℕ  using (ℕ)
open import Data.Fin    as F  using (Fin)

open import Data.Number.Result
import Data.Number.Fin  as NF
open import Data.Number.Bool as B using (#0 ; #1)

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
toℕ = F.toℕ ∘ getDigit

toℕ′ : {r : ℕ} (bd : Digit r withCarry) → ℕ
toℕ′ {r} (b ∙ d) = B.toℕ b ℕ.* r ℕ.+ toℕ d

suc : {r : ℕ} (d : Digit r) → Digit r withCarry
suc [ k ] = fmap [_] $ NF.suc k

suc-toℕ : {r : ℕ} (d : Digit r) → toℕ′ (suc d) ≡ ℕ.suc (toℕ d)
suc-toℕ [ k ] = NF.suc-toℕ k

suc-inv : {r : ℕ} (d e : Digit (ℕ.suc r)) (c : Bool) (eq : suc d ≡ (c ∙ e)) →
          if c then e ≡ [ F.zero ] else ⊤
suc-inv _     _     #0 _  = tt
suc-inv [ k ] [ l ] #1 eq = cong [_] $ NF.suc-inv k l true $ cong (fmap getDigit) eq

infix 5 _+_
_+_ : {r : ℕ} (d e : Digit r) → Digit r withCarry
[ k ] + [ l ] = fmap [_] $ k NF.+ l

_+_-toℕ : {r : ℕ} (d e : Digit r) → toℕ′ (d + e) ≡ toℕ d ℕ.+ toℕ e
_+_-toℕ [ k ] [ l ] = NF._+_-toℕ k l

infix 5 _+_′_
_+_′_ : {r :  ℕ} (d e : Digit r) (c : Bool) → Digit r withCarry
[ k ] + [ l ] ′ c = fmap [_] $ k NF.+ l ′ c

_+_′_-toℕ : {n : ℕ} (k l : Digit n) (c : Bool) → toℕ′ (k + l ′ c) ≡ B.toℕ c ℕ.+ toℕ k ℕ.+ toℕ l
[ k ] + [ l ] ′ c -toℕ = NF._+_′_-toℕ k l c
