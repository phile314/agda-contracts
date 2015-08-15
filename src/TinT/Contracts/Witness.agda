{-# OPTIONS --type-in-type #-}
module Contracts.Witness where

open import Contracts.Base
open import Relation.Nullary
open import Data.List
open import Data.Product
open import Function
open import Data.Maybe

⇔Witness' : {A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → PartIso
⇔Witness' {A} {B} d = record { LOWₐ = [] ; HIGHₐ = [] ; iso = A , ((Σ A B) , conv) }
  where
    -- we can't provide a (A → Dec (Σ A B)) here, because
    -- this would mean we have to prove that there is no
    -- such pair for all possible values of A.
    -- Using withMaybe works fine though.
    up : A → Maybe (Σ A B)
    up a = case d a of λ
      { (yes p) → just (a , p)
      ; (no ¬p) → nothing }
    conv = (withMaybe up) , (total proj₁)

{-open import Contracts.SSyn

⇔Witness : {A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → PartIsoPub
⇔Witness d = mkIsoPub (⇔Witness' d) (mkIsoInt {!!})
-}

open import Reflection
open import Contracts.SSyn
macro
--  ⇔Witness : {A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → PartIsoPub
  -- dec -> partiso
  ⇔Witness : Term → Term
  ⇔Witness dec = con (quote mkIsoPub) (arg (arg-info visible relevant) (pi') ∷ arg (arg-info visible relevant) pii ∷ [])
    where
      -- part iso
      pi' = def (quote ⇔Witness') (arg (arg-info visible relevant) dec ∷ [])
      -- part iso int
      pii = con (quote mkIsoInt) [ arg (arg-info visible relevant) (quoteTerm pi') ]
