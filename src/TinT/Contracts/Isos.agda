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
  
  ℕ⇔ℤI : PartIso
  ℕ⇔ℤI = mkPartIso1 ℤ  ℕ ((withMaybe f) , (total (ℤ.+_)))
    where f : ℤ → Maybe ℕ
          f -[1+ n ] = nothing
          f (+ n) = just n

  ℕ⇔ℤ' : PartIsoInt
  ℕ⇔ℤ' = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrapped = def (quote ℕ⇔ℤI) [] } --; wrapped = partIso}


  ℕ⇔ℤ : PartIsoPub
  ℕ⇔ℤ = record { partIso = ℕ⇔ℤI ; partIsoInt = ℕ⇔ℤ' }


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

  vec⇔listI : PartIso
  vec⇔listI = mkPartIso Set (λ _ → ⊤) (λ _ → ℕ) (λ aa _ → List aa) (λ aa n → Vec aa n)
      (λ aa _ n → (withMaybe list⇒vec) , (total toList))
    where open import Data.Unit hiding (total)


  vec⇔list' : PartIsoInt
  vec⇔list' = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrapped = def (quote vl) [] } --; wrapped = partIso }
    where vl = vec⇔listI
          open import Reflection

  vec⇔list : PartIsoPub
  vec⇔list = record { partIso = vec⇔listI ; partIsoInt = (vec⇔list') }
