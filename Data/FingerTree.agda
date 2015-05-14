module agDATA.Data.FingerTree where

open import Level
open import Algebra
open import Data.Product
open import Data.Sum
open import Data.List hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning

open import agDATA.Data.Node
open import agDATA.Data.Digit as Digit hiding (_◃_ ; _▹_ ; viewˡ ; viewˡ-prop)

infix 20 [_]
infix 10 _◂_▸_
data FingerTree
     {ℓ : Level} (R : (A : Set ℓ) (as : List A) → Set ℓ) (A : Set ℓ) :
     (as : List A) → Set ℓ where 
  ■     : FingerTree R A []
  [_]   : {as : List A} (a : R A as) → FingerTree R A as
  _◂_▸_ : {dls : List A} (dl : Digit R A dls)
          {fs  : List A} (f : FingerTree (Node R) A fs)
          {drs : List A} (dr : Digit R A drs) →
          FingerTree R A (dls ++ fs ++ drs)

digitToTree :
  {ℓ : Level} {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ} {as : List A} →
  Digit R A as → FingerTree R A as
digitToTree (One v)                    = [ v ]
digitToTree (Two vl vr)                = One vl ◂ ■ ▸ One vr
digitToTree (Three vl vc vr)           = One vl ◂ ■ ▸ Two vc vr
digitToTree (Four {vls} vl vcl vcr vr) = rew $ Two vl vcl ◂ ■ ▸ Two vcr vr
  where open Monoid (monoid _)
        rew = subst (FingerTree _ _) (assoc vls _ _)

infixr 5 _◃_
infixl 6 _▹_
_◃_ : {ℓ : Level} {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ}
      {as : List A} (a : R A as)
      {fs : List A} (f : FingerTree R A fs) →
      FingerTree R A (as ++ fs)
a ◃ ■             = rew [ a ]
  where
    open Monoid (monoid _)
    rew = subst (FingerTree _ _) (Eq.sym $ proj₂ identity _)
a ◃ [ b ]         = One a ◂ ■ ▸ One b
_◃_ {ℓ} {R} {A} {as} a (_◂_▸_ {dls} dl {fs} f {drs} dr) = [ win , fail ]′ (a Digit.◃ dl)
  where
    open Monoid (monoid A)

    win : Digit R A (as ++ dls) → FingerTree R A (as ++ dls ++ fs ++ drs)
    win adl = rew $ adl ◂ f ▸ dr
      where rew = subst (FingerTree R A) (assoc as dls (fs ++ drs))

    fail : Σ[ v ∈ List A ] Σ[ w ∈ List A ] (Digit R A v × Node R A w × as ++ dls ≡ v ++ w) →
           FingerTree R A (as ++ dls ++ fs ++ drs)
    fail (vs , ws , d , n , eq) = rew $ d ◂ n ◃ f ▸ dr
      where rew = subst (FingerTree R A) 
                $ begin 
                  vs ++ (ws ++ fs) ++ drs  ≡⟨ cong (_++_ vs) (assoc ws fs drs) ⟩
                  vs ++ ws ++ fs ++ drs    ≡⟨ Eq.sym $ assoc vs ws (fs ++ drs) ⟩
                  (vs ++ ws) ++ fs ++ drs  ≡⟨ cong (flip _++_ (fs ++ drs)) (Eq.sym eq) ⟩
                  (as ++ dls) ++ fs ++ drs ≡⟨ assoc as dls (fs ++ drs) ⟩ 
                  as ++ dls ++ fs ++ drs
                  ∎

_▹_ : {ℓ : Level} {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ}
      {fs : List A} (f : FingerTree R A fs)
      {as : List A} (a : R A as) →
      FingerTree R A (fs ++ as)
■           ▹ a = [ a ]
[ b ]       ▹ a = One b ◂ ■ ▸ One a
_▹_ {ℓ} {R} {A} (_◂_▸_ {dls} dl {fs} f {drs} dr) {as} a = [ win , fail ]′ (dr Digit.▹ a)
  where
    open Monoid (monoid A)

    win : Digit R A (drs ++ as) → FingerTree R A ((dls ++ fs ++ drs) ++ as)
    win d = rew $ dl ◂ f ▸ d
      where rew = subst (FingerTree R A) $ allButLast dls fs drs as

    fail : Σ[ v ∈ List A ] Σ[ w ∈ List A ] (Node R A v × Digit R A w × drs ++ as ≡ v ++ w) →
           FingerTree R A ((dls ++ fs ++ drs) ++ as)
    fail (vs , ws , n , d , eq) = rew $ dl ◂ f ▹ n ▸ d
      where rew = subst (FingerTree R A) $
                  begin 
                  dls ++ (fs ++ vs) ++ ws ≡⟨ cong (_++_ dls) $ assoc fs _ _ ⟩
                  dls ++ fs ++ vs ++ ws   ≡⟨ cong (_++_ dls ∘ _++_ fs) (Eq.sym eq) ⟩
                  dls ++ fs ++ drs ++ as  ≡⟨ allButLast dls fs drs as ⟩
                  (dls ++ fs ++ drs) ++ as
                  ∎

open import Data.Unit
open import Data.Empty
open import Data.Maybe

viewˡ : {ℓ : Level} {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ}
        {fs : List A} (f : (FingerTree R) A fs) →
        Viewˡ FingerTree R A fs
viewˡ ■ = ■[ refl ]
viewˡ [ a ] = a ◂ ■ [ proj₂ identity _ ] where open Monoid (monoid _)
viewˡ (dl ◂ f ▸ dr) with Digit.viewˡ dl | Digit.viewˡ-prop dl
viewˡ (dl ◂ f ▸ dr) | ■[ eq ]      | p = ⊥-elim $ p tt
viewˡ (_◂_▸_ {.(as ++ rs)} dl {fs} f {drs} dr) | _◂_[_] {as} a {rs} (inj₁ dl′) refl | w =
  a ◂ dl′ ◂ f ▸ dr [ Eq.sym $ assoc as rs (fs ++ drs) ] where open Monoid (monoid _)
viewˡ (dl ◂ f ▸ dr) | a ◂ inj₂ refl [ eq ] | w with viewˡ f
viewˡ (_◂_▸_ {dls} dl {.[]} f {drs} dr) | _◂_[_] {as} a (inj₂ refl) eq | w | ■[ refl ] =
  a ◂ digitToTree dr [ proof ]
  where open Monoid (monoid _) using (identity)
        proof : as ++ drs ≡ dls ++ drs
        proof = begin
                as ++ drs         ≡⟨ cong (flip _++_ drs) $ Eq.sym $ proj₂ identity as ⟩
                (as ++ []) ++ drs ≡⟨ cong (flip _++_ drs) eq ⟩
                dls ++ drs
                ∎
viewˡ (_◂_▸_ {.(as ++ [])} dl {.(dl′s ++ f′s)} f {drs} dr)
   | _◂_[_] {as} a (inj₂ refl) refl | w
   | _◂_[_] {dl′s} dl′ {f′s} f′ refl = a ◂ nodeToDigit dl′ ◂ f′ ▸ dr [ proof ]
  where open Monoid (monoid _)
        proof : as ++ dl′s ++ f′s ++ drs ≡ (as ++ []) ++ (dl′s ++ f′s) ++ drs
        proof = Eq.sym $ cong₂ _++_ (proj₂ identity as) (assoc dl′s f′s  drs)