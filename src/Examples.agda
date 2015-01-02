module Examples where

open import Contracts

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary



postulate
  pgcd : ℕ → ℕ → ℕ

data _divides_ (x y : ℕ) : Set where
  divs : ∃ (λ k → k * x ≡ y) →  x divides y

divs? : (x y : ℕ) → Dec (x divides y)
divs? x y = {!!}



gcd : (x y : ℕ) → Σ ℕ (λ z → (z divides x) × (z divides y))
gcd x y = {!!}
  where z = assert (ctrue ⇒ (λ x → {!(? ⇒ ?)!})) pgcd
