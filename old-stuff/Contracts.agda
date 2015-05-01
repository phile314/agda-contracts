module Contracts where

{-

how can we do higher order functions / fmap and keep the witness objects?

e.g.

map (f with true -> Nat) xs ==> [i...], witnesses wi...


Do we ever need the witness to create another contract? Not in priniciple,
as we can put the information into the result value, but we may not want to do that?

let the contract be (x => if x > 10 then result == 23 * x else x + 234)

e.g. imagine the decision function for sort:
data Sorted = No | Yes

then we could have a contract Stable => Verify order

assert (true => isSorted) sort


I cant really come up with a sensible example where the post-contract
depends on the result of the pre-contract.

So we basically can either thread through the all the witnesses. Alternativally,
put the contracts into a monad.

-}

open import Level
open import Data.Bool hiding (_∧_)
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Unit
open import Data.Empty
open import Category.Monad
open import Category.Monad.Indexed
open import Category.Applicative.Indexed
open import Relation.Binary.PropositionalEquality

{-
data Contract {ℓ₁} : Set ℓ₁ → Set ℓ₁ → Set (suc ℓ₁) where
  ⟨_⟩ : {α : Set ℓ₁} {β : Set ℓ₁} → (f : α → Dec β) → Contract α β
  _⇒_ : {α₁ α₂ : Set ℓ₁} {β₁ β₂ : Set ℓ₁} → Contract α₁ β₁ → (α₁ → β₁ → Contract α₂ β₂) → Contract (α₁ → α₂) (β₁ × β₂)
  _∧_ : {α : Set ℓ₁} {β₁ β₂ : Set ℓ₁} → Contract α (α × β₁) → Contract α (α × β₂) → Contract α (β₁ × β₂)-}


-- A contracts needs to be indexed by:
-- - The Input type
-- - The Witness type
--
-- We need both indexes, to make sure agda sees the result type
-- given the type of a contract.

data Contract {ℓ₁} : (a : Set ℓ₁) → (a → Set  ℓ₁) → Set (suc ℓ₁) where
  ⟨_⟩ : {α : Set ℓ₁} {β : α → Set ℓ₁} → (f : (a : α) → Dec (β a)) → Contract α β
  _∧_ : {α : Set ℓ₁} {β₁ β₂ : α → Set ℓ₁} → Contract α β₁ → Contract α β₂ → Contract α (λ x → (β₁ x) × (β₂ x))


postulate
  error : ∀ {a} {A : Set a} → A

checkProp : ∀ {a b} {α : Set a} {β : α → Set b} → (f : (α' : α) → Dec (β α')) → (α'' : α) → (β α'')
checkProp p x with p x
checkProp p x | yes p₁ = p₁
checkProp p x | no ¬p = error


mutual
  -- TODO check we never evaluate x twice (sharing).
  assert : ∀ {a} {α : Set a} {β : α → Set a} → (c : Contract α β) → (α → (Σ α β))
  assert ⟨ f ⟩ x  = x , checkProp f x
  assert (c₁ ∧ c₂) x with assert c₁ x | assert-≡ c₁ x
  assert (c₁ ∧ c₂) x | .x , proj₂ | refl with assert c₂ x | assert-≡ c₂ x
  assert (c₁ ∧ c₂) x | .x , proj₃ | refl | .x , proj₂ | refl = x , (proj₃ , proj₂)


  private postulate assert-≡ : ∀ {a} {α : Set a} {β : α → Set a} → (c : Contract α β) → (α' : α) → α' ≡ proj₁ (assert c α')


-- some basic contracts

ctrue : ∀ {a} {α : Set a} → Contract α (λ _ → Lift ⊤)
ctrue = ⟨ (λ x → yes (lift tt)) ⟩

private
  postulate
    cfalse-no : ⊥

-- TODO is it safe here to return bottom as witness?
cfalse : ∀ {a} {α : Set a} → Contract α (λ _ → Lift ⊥)
cfalse {a} {α} = ⟨_⟩ {a} {α} {λ _ → Lift ⊥} (λ x → no (λ x₁ → cfalse-no))

