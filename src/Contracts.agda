module Contracts where

open import Level
open import Data.Bool
open import Data.Product
open import Relation.Nullary
open import Function


data Contract {a b} : Set a → Set b → Set (suc (a ⊔ b)) where
  prop : {α : Set a} {β : Set b} → (f : α → Dec β) → Contract α β
  function : {α₁ α₂ : Set a} {β₁ β₂ : Set b} → Contract α₁ β₁ → (α₁ → Contract α₂ β₂) → Contract (α₁ → α₂) β₂
  and : {α : Set a} {β₁ β₂ : Set b} → Contract α β₁ → Contract α β₂ → Contract α (β₁ × β₂)


assert : ∀ {a b} {α : Set a} {β : Set b} → Contract α β → (α → (α × β))
assert (prop c) x = {!!}
assert (function c₁ c₂) f = {!!}
assert (and c₁ c₂) x = let (α₁ , β₁) = assert c₁ x
                           (α₂ , β₂) = assert c₂ α₁ in α₂ , (β₁ , β₂)
--assert (and c₁ c₂) x = ((assert c₂) ∘ (assert c₁)) {!!}
