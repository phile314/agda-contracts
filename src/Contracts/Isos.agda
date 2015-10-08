{-# OPTIONS --type-in-type #-}

module Contracts.Isos where

open import Contracts.Base
open import Contracts.SSyn

module NatIntIso where
  open import Data.Nat
  open import Data.Integer
  open import Data.Maybe
  open import Data.List
  open import Data.Product
  open import Reflection
  open import Data.Unit hiding (total)

  ℕ⇔ℤ : PartIsoPub
  ℕ⇔ℤ = makeIso ℕ⇔ℤ'
    where
      ℤ⇒ℕ : ℤ → Maybe ℕ
      ℤ⇒ℕ -[1+ n ] = nothing
      ℤ⇒ℕ (+ n) = just n
      ℕ⇔ℤ' = mkPartIso1 ℤ ℕ (withMaybe ℤ⇒ℕ , (total (ℤ.+_)))

module VecIso where
  open import Data.List as L
  open import Data.Nat as N
  open import Data.Maybe
  open import Data.Vec
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality
  open import Data.Product

  list⇒vec : ∀ {n : ℕ} {A : Set} → List A → Maybe (Vec A n)
  list⇒vec {n} xs with n N.≟ L.length xs
  list⇒vec xs | yes refl = just (Data.Vec.fromList xs)
  list⇒vec xs | no ¬p = nothing

  vec⇔list : PartIsoPub
  vec⇔list = makeIso vec⇔list'
    where
      vec⇔list' = record
        { ARG-a = Set
        ; ARG-l = λ _ → ⊤
        ; ARG-h = λ _ → ℕ
        ; τ-l = λ aa _ → List aa
        ; τ-h = λ aa n → Vec aa n
        ; ⇅ = λ aa _ n → (withMaybe list⇒vec) , (total toList)
        }
        where open import Data.Unit hiding (total)
