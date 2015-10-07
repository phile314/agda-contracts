{-# OPTIONS --type-in-type #-}
module ForeignContracts where

open import Contracts.SSyn
open import Contracts.Base
open import Foreign.Base

open import Reflection
macro
  assert-foreign : (ffiSpec : Term) → (contract : Term) → Term
  assert-foreign ffiSpec contract = forceTy' (deriveHighType int) lifted
    where
      open import Function
      int = surface⇒internal contract
      lowDef = (foreign-term ffiSpec (el (unknown) (deriveLowType int)))
      low = forceTy' (deriveLowType int) lowDef
      lifted = contract-apply int low
