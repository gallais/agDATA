module Data.Sized.Stream.Sequence where

open import Size
open import Data.Nat
open import Data.Number.Nat
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.Sized.Stream
open import Function
open import Relation.Binary.PropositionalEquality as PEq
open PEq.≡-Reasoning

geometric : (r u₀ : ℕ) → Stream ℕ ∞
geometric r = unfold (λ uₙ → uₙ , r * uₙ)

lookup-geometric : {r u₀ : ℕ} (k : ℕ) → lookup k (geometric r u₀) ≡ (r ^ k) * u₀
lookup-geometric {_} {u₀} zero    = +-comm 0 u₀
lookup-geometric {r} {u₀} (suc k) =
  begin
    lookup (suc k) (geometric r u₀) ≡⟨ lookup-geometric k ⟩
    r ^ k * (r * u₀)                ≡⟨ sym $ *-assoc (r ^ k) r u₀ ⟩
    r ^ k * r * u₀                  ≡⟨ cong (_* u₀) (*-comm (r ^ k) r) ⟩
    r * r ^ k * u₀
  ∎

powers : (r : ℕ) → Stream ℕ ∞
powers r = geometric r 1
