module Data.Number.Digits where

open import Algebra.Structures 
open import Data.Bool
open import Data.Nat    as ℕ using (ℕ)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin    as F using (Fin)

open import Data.Number.Result
open import Data.Number.Bool as B using (#0 ; #1)
import Data.Number.Fin  as NF
open import Data.Number.Nat
open import Data.Number.Digit as D using (Digit)

open import Data.Product
open import Data.List
open import Data.Sized.Stream as S
open import Data.Sized.Stream.Sequence
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

Digits : (r : ℕ) → Set
Digits = List ∘ Digit

toℕ : {r : ℕ} (ds : Digits r) → ℕ
toℕ     []       = 0
toℕ {r} (d ∷ ds) = D.toℕ d ℕ.+ r ℕ.* toℕ ds 

toℕ′ : {r : ℕ} (bd : Digits r withCarry) → ℕ
toℕ′ {r} (b ∙ ds) = B.toℕ b ℕ.* r ^ length ds ℕ.+ toℕ ds

shiftLeft : {r : ℕ} (ds : Digits r) → Digits r
shiftLeft {0}       = id
shiftLeft {ℕ.suc _} = D.[ F.zero ] ∷_

shiftLeft-toℕ : {r : ℕ} (ds : Digits r) → toℕ (shiftLeft ds) ≡ r ℕ.* toℕ ds
shiftLeft-toℕ {0}       []        = refl
shiftLeft-toℕ {0}       (() ∷ ds)
shiftLeft-toℕ {ℕ.suc r} ds        = refl

suc : {r : ℕ} (ds : Digits r) → Digits r withCarry
suc []       = #1 ∙ []
suc (d ∷ ds) =
  let (c₁ ∙ sd)  = D.suc d
      (c₂ ∙ sds) = if c₁ then suc ds else #0 ∙ ds
  in c₂ ∙ sd ∷ sds

suc-toℕ : {r : ℕ} (ds : Digits r) → toℕ′ (suc ds) ≡ ℕ.suc (toℕ ds)
suc-toℕ [] = refl
suc-toℕ {r} (d ∷ ds) with D.suc d | suc ds | D.suc-toℕ d | suc-toℕ ds
... | #0 ∙ sd | _        | eqsd | _     = cong (ℕ._+ r ℕ.* toℕ ds) eqsd
... | #1 ∙ sd | #0 ∙ sds | eqsd | eqsds =
  begin
    D.toℕ sd ℕ.+ r ℕ.* toℕ sds            ≡⟨ cong ((D.toℕ sd ℕ.+_) ∘ (r ℕ.*_)) eqsds ⟩
    D.toℕ sd ℕ.+ r ℕ.* ℕ.suc (toℕ ds)     ≡⟨ cong (D.toℕ sd ℕ.+_) (+-*-suc r (toℕ ds)) ⟩
    D.toℕ sd ℕ.+ (r ℕ.+ r ℕ.* toℕ ds)     ≡⟨ sym (+-assoc (D.toℕ sd) r (r ℕ.* toℕ ds)) ⟩
    D.toℕ sd ℕ.+ r ℕ.+ r ℕ.* toℕ ds       ≡⟨ cong (ℕ._+ r ℕ.* toℕ ds) (+-comm (D.toℕ sd) r) ⟩
    r ℕ.+ D.toℕ sd ℕ.+ r ℕ.* toℕ ds       ≡⟨ cong ((ℕ._+ r ℕ.* toℕ ds) ∘ (ℕ._+ D.toℕ sd)) (+-comm 0 r) ⟩
    r ℕ.+ 0 ℕ.+ D.toℕ sd ℕ.+ r ℕ.* toℕ ds ≡⟨ cong (ℕ._+ (r ℕ.* toℕ ds)) eqsd ⟩
    ℕ.suc (D.toℕ d ℕ.+ r ℕ.* toℕ ds)
  ∎
... | #1 ∙ sd | #1 ∙ sds | eqsd | eqsds rewrite +-comm (r ^ length (sd ∷ sds)) 0 =
  let ⟦sd⟧      = D.toℕ sd
      r^∣sds∣    = r ^ length sds
      r^∣sd∷sds∣ = r ^ length (sd ∷ sds)
      r*⟦ds⟧    = r ℕ.* toℕ ds
      r*⟦sds⟧   = r ℕ.* toℕ sds

      first-step : (a b c : ℕ) → a ℕ.+ (b ℕ.+ c) ≡ b ℕ.+ (a ℕ.+ c)
      first-step a b c =
        begin
          a ℕ.+ (b ℕ.+ c) ≡⟨ sym (+-assoc a b c) ⟩
          a ℕ.+ b ℕ.+ c   ≡⟨ cong (ℕ._+ c) (+-comm a b) ⟩
          b ℕ.+ a ℕ.+ c   ≡⟨ +-assoc b a c ⟩
          b ℕ.+ (a ℕ.+ c)
        ∎

      second-step : r^∣sd∷sds∣ ℕ.+ r*⟦sds⟧ ≡ r ℕ.+ r ℕ.* toℕ ds
      second-step =
        let open IsCommutativeSemiring isCommutativeSemiring using (distrib) in
        begin
          r^∣sd∷sds∣ ℕ.+ r*⟦sds⟧            ≡⟨ sym (proj₁ distrib r (r^∣sds∣) (toℕ sds)) ⟩
          r ℕ.* (r^∣sds∣ ℕ.+ toℕ sds)       ≡⟨ cong ((r ℕ.*_) ∘ (ℕ._+ toℕ sds)) (+-comm 0 (r^∣sds∣)) ⟩
          r ℕ.* (r^∣sds∣ ℕ.+ 0 ℕ.+ toℕ sds) ≡⟨ cong (r ℕ.*_) eqsds ⟩
          r ℕ.* ℕ.suc (toℕ ds)             ≡⟨ +-*-suc r (toℕ ds) ⟩
          r ℕ.+ r ℕ.* toℕ ds
        ∎
      
      final-step : ⟦sd⟧ ℕ.+ r ≡  ℕ.suc (D.toℕ d)
      final-step = 
        begin
          ⟦sd⟧ ℕ.+ r         ≡⟨ +-comm ⟦sd⟧ r ⟩
          r ℕ.+ ⟦sd⟧         ≡⟨ cong (ℕ._+ ⟦sd⟧) (+-comm 0 r) ⟩
          r ℕ.+ 0 ℕ.+ ⟦sd⟧   ≡⟨ eqsd ⟩
          ℕ.suc (D.toℕ d)
        ∎
  in
  
  begin
    r^∣sd∷sds∣ ℕ.+ (⟦sd⟧ ℕ.+ r*⟦sds⟧) ≡⟨ first-step r^∣sd∷sds∣ ⟦sd⟧ r*⟦sds⟧ ⟩
    ⟦sd⟧ ℕ.+ (r^∣sd∷sds∣ ℕ.+ r*⟦sds⟧) ≡⟨ cong (⟦sd⟧ ℕ.+_) second-step ⟩
    ⟦sd⟧ ℕ.+ (r ℕ.+ r*⟦ds⟧)          ≡⟨ sym (+-assoc (⟦sd⟧) r r*⟦ds⟧) ⟩
    ⟦sd⟧ ℕ.+ r ℕ.+ r*⟦ds⟧            ≡⟨ cong (ℕ._+ r*⟦ds⟧) final-step ⟩
    ℕ.suc (D.toℕ d ℕ.+ r*⟦ds⟧)
  ∎

infix 5 _+_′_
_+_′_ : {r : ℕ} (ds es : Digits r) (c : Bool) → Digits r withCarry
[]       + es       ′ c = if c then suc es else #0 ∙ es
ds       + []       ′ c = if c then suc ds else #0 ∙ ds
(d ∷ ds) + (e ∷ es) ′ c =
  let (c′ ∙ d+e+c)    = d D.+ e ′ c
      (cf ∙ ds+es+c′) = ds + es ′ c′
  in cf ∙ d+e+c ∷ ds+es+c′

infix 5 _+_
_+_ : {r : ℕ} (ds es : Digits r) → Digits r withCarry
ds + es = ds + es ′ #0
