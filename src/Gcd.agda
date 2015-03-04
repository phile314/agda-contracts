module Gcd where

open import Contracts

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Fin

postulate
  divs-dec-helper : ⊥
  HsInteger : Set
  hs-gcd1 : HsInteger → HsInteger → HsInteger
  toHsInteger : ℕ → HsInteger
  fromHsInteger : HsInteger → Dec ℕ

hs-gcd : ℕ → ℕ → ℕ
hs-gcd x y = proj₂ (assert ⟨ fromHsInteger ⟩ (hs-gcd1 (toHsInteger x) (toHsInteger y)))

data _divides_ (x y : ℕ) : Set where
  divs : ∃ (λ k → k * x ≡ y) →  x divides y

divisor-not0 : ∀ {x} → (zero divides x) → ⊥
divisor-not0 {x} (divs (proj₁ , proj₂)) = divs-dec-helper

divs? : (x y : ℕ) → Dec (x divides y)
divs? zero (suc y) = no (λ x₁ → ⊥-elim (divisor-not0 x₁))
divs? zero zero = yes (divs (zero , refl))
divs? (suc x) y with y divMod (suc x)
divs? (suc x) y | result quotient zero property = yes (divs (quotient , (sym property)))
divs? (suc x) y | result quotient (suc remainder) property = no (λ x₁ → divs-dec-helper)

gcd : (x y : ℕ) → Σ ℕ (λ z → ((z divides x) × (z divides y)))
gcd x y = let r = hs-gcd x y
              c : Contract ℕ (λ z → (z divides x) × (z divides y))
              c = ⟨ (λ a → divs? a x) ⟩ ∧ ⟨ (λ a → divs? a y) ⟩
           in assert c r
