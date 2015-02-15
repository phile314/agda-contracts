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
open import Category.Monad
open import Category.Monad.Indexed
open import Category.Applicative.Indexed

{-
data Contract {ℓ₁} : Set ℓ₁ → Set ℓ₁ → Set (suc ℓ₁) where
  ⟨_⟩ : {α : Set ℓ₁} {β : Set ℓ₁} → (f : α → Dec β) → Contract α β
  _⇒_ : {α₁ α₂ : Set ℓ₁} {β₁ β₂ : Set ℓ₁} → Contract α₁ β₁ → (α₁ → β₁ → Contract α₂ β₂) → Contract (α₁ → α₂) (β₁ × β₂)
  _∧_ : {α : Set ℓ₁} {β₁ β₂ : Set ℓ₁} → Contract α (α × β₁) → Contract α (α × β₂) → Contract α (β₁ × β₂)-}
data Contract {ℓ₁} : Set ℓ₁ → Set (suc ℓ₁) where
  ⟨_⟩ : {α : Set ℓ₁} {β : Set ℓ₁} → (f : α → Dec β) → Contract α
  _⇒_ : {α₁ α₂ : Set ℓ₁} → Contract α₁ → (α₁ → Contract α₂) → Contract (α₁ → α₂)
  _∧_ : {α : Set ℓ₁} → Contract α → Contract α → Contract α

-- in the end, we get a list of witnesses. But should we just use some sort
-- of (heterogenous) list, or should we do an explicit encoding?
-- lets just use nested pairs for this right now.

-- extract witness types from contract
contractToW : ∀ {a} {α : Set a} → Contract α → Set a
contractToW (⟨_⟩ {α} {β} f) = (α × β)
contractToW (_⇒_ {α₁} {α₂} c₁ c₂) = (x : α₁) → (α₂ × contractToW (c₂ x))
contractToW (_∧_ {α} c₁ c₂) = α × (contractToW c₁ × contractToW c₂)


postulate
  error : ∀ {a} {A : Set a} → A

checkProp : ∀ {a b} {α : Set a} {β : Set b} → (f : α → Dec β) → (α → (α × β))
checkProp p x with p x
checkProp p x | yes p₁ = x , p₁
checkProp p x | no ¬p = error

checkFun : ∀ {ℓ} {α₁ α₂ β₁ β₂ : Set ℓ} → (α₁ → α₁ × β₁) → (α₁ → α₂ → α₂ × β₂) → (α₁ →  α₂) → α₁ → α₂ × β₂
checkFun c1 c2 f x with c1 x
checkFun c1 c2 f x | Α₁ , Β₁ with f Α₁
... | Α₂ with c2 Α₁ Α₂
checkFun c1 c2 f x | Α₁ , Β₁ | _ | Α₂ , Β₂ = {!!}


assert : ∀ {a} {α : Set a} → (c : Contract α) → (α → (contractToW c))
assert ⟨ f ⟩ x = checkProp f x
assert (c₁ ⇒ c₂) f = λ x → checkFun {!assert c₁!} {!assert ∘ c₂!} f x
assert (c₁ ∧ c₂) x with assert c₁ x | assert c₂ x
... | a | b = x , (a , b)

--let (α₁ , β₁) = assert c₁ x
--                         (α₂ , β₂) = assert c₂ α₁ in α₂ , (β₁ , β₂)

-- we want to store the witness types in the index
IAssertT : ∀ {i f} {I : Set i} → (I → Set f) → (Set f → Set f) → IFun I f
IAssertT = {!!}


{-checkFun : ∀ {ℓ} {α₁ α₂ β₁ β₂ : Set ℓ} → (α₁ → α₁ × β₁) → (α₁ → α₂ → α₂ × β₂) → (α₁ →  α₂) → α₁ → α₂ × β₁ × β₂
checkFun c1 c2 f x with c1 x
checkFun c1 c2 f x | Α₁ , Β₁ with f Α₁
... | Α₂ with c2 Α₁ Α₂
checkFun c1 c2 f x | Α₁ , Β₁ | _ | Α₂ , Β₂ = Α₂ , (Β₁ , Β₂)
-}
-- we should try to get agda to see that this terminates instead...
{--# TERMINATING #-}
{-assert : ∀ {a} {α : Set a} {β : Set a} → Contract α β → (α → β)
assert (prop c) x = checkProp c x
assert (c₁ ⇒ c₂) f = λ x → checkFun (assert c₁) (assert ∘ c₂) f x
assert (and c₁ c₂) x = let (α₁ , β₁) = assert c₁ x
                           (α₂ , β₂) = assert c₂ α₁ in α₂ , (β₁ , β₂)
-}

-- contract construction functions

{-ctrue : ∀ {a} {α : Set a} → Contract α (α × Lift ⊤)
ctrue = prop (λ x → yes (lift tt))-}
