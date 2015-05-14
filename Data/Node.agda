module agDATA.Data.Node where

open import Level
open import Data.List

data Node
     {ℓ : Level} (R : (A : Set ℓ) (as : List A) → Set ℓ) (A : Set ℓ) :
     (as : List A) → Set ℓ where
  node2 : {vls : List A} (vl : R A vls) →
          {vrs : List A} (vr : R A vrs) →
          Node R A (vls ++ vrs)
  node3 : {vls : List A} (vl : R A vls) →
          {vcs : List A} (vc : R A vcs) →
          {vrs : List A} (vr : R A vrs) →
          Node R A (vls ++ vcs ++ vrs)