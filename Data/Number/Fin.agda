module Data.Number.Fin where

open import Data.Unit
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin as F using (Fin)
open import Data.Fin.Case
import Data.Fin.Properties as FProp
open import Data.Bool
open import Data.Bool.Properties
open import Data.Number.Result
open import Data.Number.Bool as B using (#0 ; #1)
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning

suc : {n : ℕ} (k : Fin n) → Fin n withCarry
suc {0} ()
suc {ℕ.suc n} k =
  case caseFin₁ k of λ
    { (inj₁ pr)       → #1 ∙ F.zero
    ; (inj₂ (l , pr)) → #0 ∙ F.suc l
    }

suc-inv : {n : ℕ} (k l : Fin (ℕ.suc n)) (b : Bool) (eq : suc k ≡ (b ∙ l)) →
          if b then l ≡ F.zero else ⊤
suc-inv k l b eq with caseFin₁ k
suc-inv _ _ _ refl | inj₁ _ = refl
suc-inv _ _ _ refl | inj₂ _ = tt

toℕ′ : {n : ℕ} → Fin n withCarry → ℕ
toℕ′ {n} (b ∙ k) = (B.toℕ b ℕ.* n) ℕ.+ F.toℕ k

suc-toℕ : {n : ℕ} (d : Fin n) → toℕ′ (suc d) ≡ ℕ.suc (F.toℕ d)
suc-toℕ {0} ()
suc-toℕ {ℕ.suc n} k with caseFin₁ k
... | inj₁ eq
  rewrite eq | +-right-identity n
             | +-right-identity n = cong ℕ.suc (sym $ FProp.to-from _)
... | inj₂ (l , eq) rewrite eq = cong ℕ.suc (sym $ FProp.inject₁-lemma _)

plus : {n m : ℕ} (le : m ℕ.≤ n) (k : Fin m) (l : Fin n) → Fin n withCarry
plus le         F.zero    l = #0 ∙ l
plus (ℕ.s≤s le) (F.suc k) l =
  let (b ∙ 1+l) = suc l in
  if b then #1 ∙ F.inject≤ k (≤-step le)
       else plus (≤-step le) k 1+l

plus-toℕ : {n m : ℕ} (le : m ℕ.≤ n) (k : Fin m) (l : Fin n) →
           toℕ′ (plus le k l) ≡ F.toℕ k ℕ.+ F.toℕ l
plus-toℕ le F.zero l = refl
plus-toℕ {ℕ.suc n} (ℕ.s≤s le) (F.suc k) l with caseFin₁ l
... | inj₁ eq rewrite eq | +-right-identity n = cong ℕ.suc $
  begin
    n ℕ.+ F.toℕ (F.inject≤ k (≤-step le)) ≡⟨ cong (n ℕ.+_) (FProp.inject≤-lemma k _) ⟩
    n ℕ.+ F.toℕ k                         ≡⟨ cong (ℕ._+ (F.toℕ k)) (sym $ FProp.to-from n) ⟩
    F.toℕ (F.fromℕ n) ℕ.+ F.toℕ k         ≡⟨ +-comm _ (F.toℕ k) ⟩
    F.toℕ k ℕ.+ F.toℕ (F.fromℕ n)
  ∎
... | inj₂ (v , eq) =
  begin
    toℕ′ (plus (≤-step le) k (F.suc v)) ≡⟨ plus-toℕ (≤-step le) k (F.suc v) ⟩
    F.toℕ k ℕ.+ ℕ.suc (F.toℕ v)         ≡⟨ +-suc (F.toℕ k) (F.toℕ v)        ⟩
    ℕ.suc (F.toℕ k ℕ.+ F.toℕ v)         ≡⟨ cong (ℕ.suc ∘ (F.toℕ k ℕ.+_))
                                                (sym $ trans (cong F.toℕ eq) (FProp.inject₁-lemma v)) ⟩
    ℕ.suc (F.toℕ k ℕ.+ F.toℕ l)
  ∎

infix 5 _+_
_+_ : {n : ℕ} (k l : Fin n) → Fin n withCarry
_+_ = plus (≤′⇒≤ ℕ.≤′-refl)

_+_-toℕ : {n : ℕ} (k l : Fin n) → toℕ′ (k + l) ≡ F.toℕ k ℕ.+ F.toℕ l
_+_-toℕ = plus-toℕ (≤′⇒≤ ℕ.≤′-refl)

infix 5 _+_′_
_+_′_ : {n : ℕ} (k l : Fin n) (c : Bool) → Fin n withCarry
k + l ′ c =
  let (c₁ ∙ sk)   = if c then suc k else #0 ∙ k
      (c₂ ∙ sk+l) = sk + l
  in (c₁ ∨ c₂) ∙ sk+l

_+_′_-toℕ : {n : ℕ} (k l : Fin n) (c : Bool) → toℕ′ (k + l ′ c) ≡ B.toℕ c ℕ.+ F.toℕ k ℕ.+ F.toℕ l
_+_′_-toℕ {0} ()
_+_′_-toℕ k l false = _+_-toℕ k l
_+_′_-toℕ {ℕ.suc n} k l true  with suc k | suc-toℕ k | suc-inv k (value (suc k)) (carry (suc k)) refl
... | (#0 ∙ sk) | eq | pr rewrite _+_-toℕ sk l | eq = refl
... | (#1 ∙ sk) | eq | pr rewrite pr =
  begin
    ℕ.suc (n ℕ.+ ℕ.zero ℕ.+ F.toℕ l)            ≡⟨ cong (ℕ._+ F.toℕ l) (sym $ +-right-identity (ℕ.suc n ℕ.+ 0)) ⟩
    ℕ.suc (n ℕ.+ ℕ.zero ℕ.+ ℕ.zero ℕ.+ F.toℕ l) ≡⟨ cong (ℕ._+ F.toℕ l) eq ⟩
    ℕ.suc (F.toℕ k) ℕ.+ F.toℕ l
  ∎
