{-# OPTIONS --type-in-type #-}

module Contracts.BaseExample where

open import Contracts.Isos

tt' = quoteTerm tt
  where open import Data.Unit

module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Contracts.Base
  open import Data.Maybe
  open import Data.Product
  open import Data.List
  open import Data.Vec
  open NatIntIso
  open import Contracts.SSyn

  import Level

  ℕ⇔ℤ' = PartIsoPub.partIsoInt ℕ⇔ℤ

  -- the internal AST representation of the "⟨ ℕ⇔ℤ ⟩⇒ ⟨ ℕ⇔ℤ ⟩⇒ ⟨ ℕ⇔ℤ ⟩" contract
  addType : InternalSyn 0
  addType = π ( iso ℕ⇔ℤ' tt' tt' tt' ) ∣ Keep ⇒ (π (iso ℕ⇔ℤ' tt' tt' tt') ∣ Keep ⇒ (iso ℕ⇔ℤ' tt' tt' tt'))

  -- the ffi declaration
  add' : ℤ → ℤ → ℤ
  add' = Data.Integer._+_

  -- the wrapper, which has the type ℕ → ℕ → ℕ
  -- this is the thing we want in the end.
  -- The contract-apply function does the heavy lifting,
  -- by producing a term which inserts the contracts checks where necessary.
  add : unquote (deriveHighType addType)
  add = unquote (contract-apply addType (def (quote add') [])) -- unquote (ffi-lift addType (quote add'))
    where open import Reflection


module MapEx where
  open VecIso
  open NatIntIso
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Integer
  open import Data.Nat
  import Data.Vec as V
  open import Reflection
  open import Contracts.SSyn

  ℕ⇔ℤ' = PartIsoPub.partIsoInt ℕ⇔ℤ

  mapImpl : (ℤ → ℤ) → L.List ℤ → L.List ℤ
  mapImpl f L.[] = L.[]
  mapImpl f (x L.∷ xs) = f x L.∷ mapImpl f xs

  -- map higher order fun, where we convert the inputs of the higher order thingie
  -- Contract: (⟨ ℕ⇔ℤ ⟩⇒ ⟨ ℕ⇔ℤ ⟩) ⇒ List ℤ ⇒ List ℤ
  mapNZType : InternalSyn 0
  mapNZType =
      π (
        π (iso ℕ⇔ℤ' tt' tt' tt') ∣ Keep ⇒ (iso ℕ⇔ℤ' tt' tt' tt')
        ) ∣ Keep
    ⇒ (π (agda-ty (quoteTerm (L.List ℤ))) ∣ Keep
    ⇒ (agda-ty (quoteTerm (L.List ℤ))))

  myMap : unquote (deriveHighType mapNZType)
  myMap = unquote (contract-apply mapNZType (quoteTerm mapImpl))


module DepSimple where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin
  import Data.Vec as V
  open import Reflection

  f : (n : ℕ) (A : Set) → List A
  f n A = []

  vec⇔list' = PartIsoPub.partIsoInt vec⇔list
    where open import Contracts.SSyn

  -- Contract: ⟨ n : ℕ ⟩⇒ ⟨ A : Set ⟩ ⇒ ⟨ vec⇔list A n ⟩
  fNZType : InternalSyn 0
  fNZType =
    π (agda-ty (def (quote ℕ) [])) ∣ Keep -- n
    ⇒ (π (agda-ty (quoteTerm Set)) ∣ Keep -- A
    ⇒ (iso (vec⇔list') (var 0 []) tt' (var 1 []) ))

  import Data.Nat.Base
  import Data.List.Base
  import Data.Vec

  f' : unquote (deriveHighType fNZType)
  f' = unquote (contract-apply fNZType (def (quote f) []))

