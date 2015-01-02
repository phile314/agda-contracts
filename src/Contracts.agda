module Contracts where

open import Level
open import Data.Bool
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Unit

postulate
  error : ∀ {a} {A : Set a} → A

data Contract {ℓ₁} : Set ℓ₁ → Set ℓ₁ → Set (suc ℓ₁) where
  prop : {α : Set ℓ₁} {β : Set ℓ₁} → (f : α → Dec β) → Contract α (α × β)
  _⇒_ : {α₁ α₂ : Set ℓ₁} {β₁ β₂ : Set ℓ₁} → Contract α₁ (α₁ × β₁) → (α₁ → Contract α₂ (α₂ × β₂)) → Contract (α₁ → α₂) (α₁ → α₂ × (β₁ × β₂))
  and : {α : Set ℓ₁} {β₁ β₂ : Set ℓ₁} → Contract α (α × β₁) → Contract α (α × β₂) → Contract α (α × (β₁ × β₂))


checkProp : ∀ {a b} {α : Set a} {β : Set b} → (f : α → Dec β) → (α → (α × β))
checkProp p x with p x
checkProp p x | yes p₁ = x , p₁
checkProp p x | no ¬p = error

checkFun : ∀ {ℓ} {α₁ α₂ β₁ β₂ : Set ℓ} → (α₁ → α₁ × β₁) → (α₁ → α₂ → α₂ × β₂) → (α₁ →  α₂) → α₁ → α₂ × β₁ × β₂
checkFun c1 c2 f x with c1 x
checkFun c1 c2 f x | Α₁ , Β₁ with f Α₁
... | Α₂ with c2 Α₁ Α₂
checkFun c1 c2 f x | Α₁ , Β₁ | _ | Α₂ , Β₂ = Α₂ , (Β₁ , Β₂)

-- we should try to get agda to see that this terminates instead...
{-# TERMINATING #-}
assert : ∀ {a} {α : Set a} {β : Set a} → Contract α β → (α → β)
assert (prop c) x = checkProp c x
assert (c₁ ⇒ c₂) f = λ x → checkFun (assert c₁) (assert ∘ c₂) f x
assert (and c₁ c₂) x = let (α₁ , β₁) = assert c₁ x
                           (α₂ , β₂) = assert c₂ α₁ in α₂ , (β₁ , β₂)


-- contract construction functions

ctrue : ∀ {a} {α : Set a} → Contract α (α × Lift ⊤)
ctrue = prop (λ x → yes (lift tt))
