{-# OPTIONS --type-in-type #-}
module ForeignContracts where

open import Contracts.SSyn
open import Contracts.Base
open import Foreign.Base

open import Reflection
macro
  assert-foreign : (ffiSpec : Term) → (contract : Term) → Term
  assert-foreign ffiSpec contract = forceTy' (getAgdaHighType t) lifted
    where
      open import Function
      t = ast⇒T' {0} contract
      lowDef = (foreign-term ffiSpec (el (unknown) (getAgdaLowType t)))
      low = forceTy' (getAgdaLowType t) lowDef
      lifted = ffi-lift t low

open import Contracts.Isos
open import Data.Nat

open import Data.Integer
open NatIntIso
open FunImport
open import Data.Product
open import Data.List
open import Data.Unit

k : Term
k = quoteTerm (makeContract (⟨ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩))

g = ast⇒T' {0} k

ffiSpec = quoteTerm (Call RuntimeError)

lowDef = (foreign-term ffiSpec (el (unknown) (getAgdaLowType g)))
low = forceTy' (getAgdaLowType g) lowDef
lifted = ffi-lift g low

l = {! (lifted)!}

m : ℤ --unquote (getAgdaLowType g)
m = foreign (Call RuntimeError) (unquote (getAgdaLowType g))

n = unquote (forceTy' (getAgdaLowType g) (def (quote m) []))
  where open import Data.List

o = {!quoteTerm (Call RuntimeError)!}

postulate x : ℤ → ℤ

test : ℕ --ℕ → ℕ
test = {- {!assert-foreign (Call RuntimeError) (makeContract (⟨ _ ∷ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩⇒ ⟨ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩))!} -}
  assert-foreign (Call RuntimeError) (makeContract (⟨ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩))
  where
    open import Data.Integer
    open NatIntIso
    open FunImport
    open import Data.Product
    open import Data.Unit
