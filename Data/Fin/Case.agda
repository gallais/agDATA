module Data.Fin.Case where

open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as F using (Fin)
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

caseFin₁ : {n : ℕ} (k : Fin (ℕ.suc n)) → k ≡ F.fromℕ n
                                      ⊎ ∃ λ l → k ≡ F.inject₁ l
caseFin₁ {0}       F.zero     = inj₁ refl
caseFin₁ {ℕ.suc n} F.zero     = inj₂ (F.zero , refl)
caseFin₁ {0}       (F.suc ())
caseFin₁ {ℕ.suc n} (F.suc k)  =
  case caseFin₁ k of λ
    { (inj₁ pr)       → inj₁ (cong F.suc pr)
    ; (inj₂ (l , pr)) → inj₂ (F.suc l , cong F.suc pr)
    }

caseFin : {n : ℕ} (m : ℕ) (k : Fin (m ℕ.+ n)) → (∃ λ (l : Fin n) → k ≡ F.raise m l)
                                              ⊎ (∃ λ (l : Fin m) → k ≡ F.inject+ n l)
caseFin ℕ.zero    k           = inj₁ (k , refl)
caseFin (ℕ.suc m) Fin.zero    = inj₂ (Fin.zero , refl)
caseFin (ℕ.suc m) (Fin.suc k) =
  case caseFin m k of λ
     { (inj₁ (l , pr)) → inj₁ (l , cong F.suc pr)
     ; (inj₂ (l , pr)) → inj₂ (F.suc l , cong F.suc pr)
     }
