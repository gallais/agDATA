module agDATA.Data.Digit where

open import Level
open import Algebra
open import Data.Product
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Sum
open import Data.List hiding ([_])
open import Function
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning

open import agDATA.Data.Node

allButLast : {ℓ : Level} {A : Set ℓ} (vls vcs vrs as : List A) →
             vls ++ vcs ++ vrs ++ as ≡ (vls ++ vcs ++ vrs) ++ as
allButLast vls vcs vrs as =
  let open Monoid (monoid _)
  in begin
     vls ++ vcs ++ vrs ++ as     ≡⟨ Eq.sym $ assoc vls vcs (vrs ++ as) ⟩
     (vls ++ vcs) ++ vrs ++ as   ≡⟨ Eq.sym $ assoc (vls ++ vcs) vrs as ⟩
     ((vls ++ vcs) ++ vrs) ++ as ≡⟨ cong (flip _++_ as) (assoc vls vcs vrs) ⟩
     (vls ++ vcs ++ vrs) ++ as
     ∎

data Digit
     {ℓ : Level} (R : (A : Set ℓ) (as : List A) → Set ℓ) (A : Set ℓ) :
     (as : List A) → Set ℓ where
  One   : {vs : List A} (v : R A vs) → Digit R A vs
  Two   : {vls : List A} (vl : R A vls) →
          {vrs : List A} (vr : R A vrs) →
          Digit R A (vls ++ vrs)
  Three : {vls : List A} (vl : R A vls) →
          {vcs : List A} (vc : R A vcs) →
          {vrs : List A} (vr : R A vrs) →
          Digit R A (vls ++ vcs ++ vrs)
  Four  : {vls : List A} (vl : R A vls) →
          {vcls : List A} (vcl : R A vcls) →
          {vcrs : List A} (vcr : R A vcrs) →
          {vrs : List A} (vr : R A vrs) →
          Digit R A (vls ++ vcls ++ vcrs ++ vrs)

nodeToDigit :
  {ℓ : Level} {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ} {as : List A}
  (n : Node R A as) → Digit R A as
nodeToDigit (node2 vl vr)    = Two vl vr
nodeToDigit (node3 vl vc vr) = Three vl vc vr

infixr 5 _◃_
infixl 6 _▹_

_◃_ : {ℓ : Level} {R : (A : Set ℓ)(as : List A) → Set ℓ} {A : Set ℓ}
      {as : List A} (a : R A as)
      {ds : List A} (d : Digit R A ds) →
        Digit R A (as ++ ds)
      ⊎ Σ[ v ∈ List A ] Σ[ w ∈ List A ]
        (Digit R A v × Node R A w × as ++ ds ≡ v ++ w )
a ◃ One v               = inj₁ $ Two a v
a ◃ Two vl vr           = inj₁ $ Three a vl vr
a ◃ Three vl vc vr      = inj₁ $ Four a vl vc vr
_◃_ {as = as} a (Four vl vcl vcr vr) = inj₂ $ , , Two a vl , node3 vcl vcr vr , Eq.sym (assoc as _ _)
  where open Monoid (monoid _)

_▹_ : {ℓ : Level} {R : (A : Set ℓ)(as : List A) → Set ℓ} {A : Set ℓ}
      {ds : List A} (d : Digit R A ds)
      {as : List A} (a : R A as) →
        Digit R A (ds ++ as)
      ⊎ Σ[ v ∈ List A ] Σ[ w ∈ List A ]
        (Node R A v × Digit R A w × ds ++ as ≡ v ++ w )
One v              ▹ a = inj₁ $ Two v a
_▹_ (Two {vls} vl vr) a = inj₁ $ rew $ Three vl vr a
  where
    open Monoid (monoid _)
    rew = subst (Digit _ _) (Eq.sym $ assoc vls _ _)
_▹_ (Three {vls} vl {vcs} vc {vrs} vr) {as} a = inj₁ $ rew $ Four vl vc vr a
  where
    rew = subst (Digit _ _) $ allButLast vls vcs vrs as 
_▹_ (Four {vls} vl {vcls} vcl {vcrs} vcr {vrs} vr) {as} a =
  inj₂ $ , , node3 vl vcl vcr , Two vr a , proof
  where
    open Monoid (monoid _)
    proof = begin
            (vls ++ vcls ++ vcrs ++ vrs) ++ as     ≡⟨ cong (flip _++_ as) $ Eq.sym $ assoc vls vcls _ ⟩
            ((vls ++ vcls) ++ vcrs ++ vrs) ++ as   ≡⟨ cong (flip _++_ as) $ Eq.sym $ assoc (vls ++ vcls) _ _ ⟩
            (((vls ++ vcls) ++ vcrs) ++ vrs) ++ as ≡⟨ assoc ((vls ++ vcls) ++ vcrs) _ _ ⟩
            ((vls ++ vcls) ++ vcrs) ++ vrs ++ as   ≡⟨ cong (λ xs → xs ++ vrs ++ as) $ assoc vls _ _ ⟩
            (vls ++ vcls ++ vcrs) ++ vrs ++ as
            ∎

infix 5 ■[_]
infixl 5 _◂_[_]
data Viewˡ {ℓ : Level}
     (S : (R : (A : Set ℓ) (as : List A) → Set ℓ) (A : Set ℓ) (as : List A) → Set ℓ)
     (R : (A : Set ℓ) (as : List A) → Set ℓ)
     (A : Set ℓ) : (as : List A) → Set ℓ  where
  ■[_]   : {as : List A} (eq : as ≡ []) → Viewˡ S R A as
  _◂_[_] : {as : List A} (a : R A as) {rs : List A} (r : S R A rs)
           {vs : List A} (eq : as ++ rs ≡ vs) → Viewˡ S R A vs

viewˡ : {ℓ : Level} {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ}
        {ds : List A} (f : Digit R A ds) →
        Viewˡ (λ R A as → Digit R A as ⊎ as ≡ []) R A ds
viewˡ (One v)              = v  ◂ inj₂ refl               [ (let open Monoid (monoid _) in proj₂ identity _) ]
viewˡ (Two vl vr)          = vl ◂ inj₁ (One vr)           [ refl ]
viewˡ (Three vl vc vr)     = vl ◂ inj₁ (Two vc vr)        [ refl ]
viewˡ (Four vl vcl vcr vr) = vl ◂ inj₁ (Three vcl vcr vr) [ refl ]

open import Data.Bool
open import Data.Empty

is■ : {ℓ : Level}
      {S : (R : (A : Set ℓ) (as : List A) → Set ℓ) (A : Set ℓ) (as : List A) → Set ℓ}
      {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ} {as : List A}
      (v : Viewˡ S R A as) → Bool
is■ ■[ eq ]        = true
is■ (a ◂ r [ eq ]) = false

viewˡ-prop :
   {ℓ : Level} {R : (A : Set ℓ) (as : List A) → Set ℓ} {A : Set ℓ}
   {ds : List A} (f : Digit R A ds) → T (is■ $ viewˡ f) → ⊥
viewˡ-prop (One v)              = id
viewˡ-prop (Two vl vr)          = id
viewˡ-prop (Three vl vc vr)     = id
viewˡ-prop (Four vl vcl vcr vr) = id