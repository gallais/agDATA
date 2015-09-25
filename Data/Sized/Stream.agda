module Data.Sized.Stream where

open import Level
open import Size
open import Data.Unit
open import Data.Nat
open import Data.Product hiding (map)
open import Data.List    hiding (take; unfold; map; zipWith)
open import Function

record Stream {ℓ : Level} (A : Set ℓ) (i : Size) : Set ℓ where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream A j

take : {ℓ : Level} {A : Set ℓ} (k : ℕ) (as : Stream A ∞) → List A
take 0       as = []
take (suc n) as = Stream.head as ∷ take n (Stream.tail as)

lookup : {ℓ : Level} {A : Set ℓ} (k : ℕ) (as : Stream A ∞) → A
lookup 0       as = Stream.head as
lookup (suc k) as = lookup k $ Stream.tail as

unfold : {ℓ ℓ′ : Level} {A : Set ℓ} {S : Set ℓ′} (n : S → A × S) (s : S) → Stream A ∞
Stream.head (unfold n s) = proj₁ (n s)
Stream.tail (unfold n s) = unfold n (proj₂ $ n s)

pure : {ℓ : Level} {A : Set ℓ} (a : A) → Stream A ∞
pure a = unfold (λ _ → a , tt) tt

app : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} (fs : Stream (A → B) ∞) (as : Stream A ∞) → Stream B ∞
Stream.head (app fs as) = Stream.head fs $ Stream.head as
Stream.tail (app fs as) = app (Stream.tail fs) (Stream.tail as)

map : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} (f : A → B) (as : Stream A ∞) → Stream B ∞
map f = app (pure f)

bind : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} (as : Stream A ∞) (fs : A → Stream B ∞) → Stream B ∞
Stream.head (bind as fs) = Stream.head $ fs $ Stream.head as
Stream.tail (bind as fs) = bind (Stream.tail as) (λ a → Stream.tail $ fs a)

zipWith : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B → C) (as : Stream A ∞) (bs : Stream B ∞) → Stream C ∞
zipWith f = app ∘ app (pure f)

zipWithˡ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
           (f : A → B → C) (as : List A) (bs : Stream B ∞) → List C
zipWithˡ f []       bs = []
zipWithˡ f (a ∷ as) bs = f a (Stream.head bs) ∷ zipWithˡ f as (Stream.tail bs)

zipWithʳ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
           (f : A → B → C) (as : Stream A ∞) (bs : List B) → List C
zipWithʳ = flip ∘ zipWithˡ ∘ flip
