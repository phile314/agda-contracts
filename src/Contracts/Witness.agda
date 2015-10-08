{-# OPTIONS --type-in-type #-}

-- Defines a parameterized partial isomorphism to handle refined types:
-- A ⇔ Σ A B

module Contracts.Witness where

open import Contracts.Base
open import Relation.Nullary
open import Data.List
open import Data.Product
open import Function
open import Data.Maybe

open import Data.Unit hiding (total)

⇔Witness' : PartIso
⇔Witness' = record
  { ARG-a = Σ Set (λ val-ty → Σ (val-ty → Set) (λ wit-ty → (b : val-ty) → Dec (wit-ty b)))
  ; ARG-l = λ _ → ⊤
  ; ARG-h = λ _ → ⊤
  ; τ-l = λ aa _ → proj₁ aa
  ; τ-h = λ aa _ → Σ (proj₁ aa) (proj₁ (proj₂ aa))
  ; ⇅ = λ aa _ _ →
    let dec = proj₂ $ proj₂ aa
        up = λ x → case dec x of λ
          { (yes p) → just (x , p)
          ; (no ¬p) → nothing }
     in withMaybe up , total proj₁
  }


-- for some strange reason, we can't use the makeIso macro here.
-- just create the boilerplate code by hand...

open import Reflection

⇔WitnessInt : PartIsoInt
⇔WitnessInt = record { wrapped = def (quote ⇔Witness') [] }

open import Contracts.SSyn

⇔Witness : PartIsoPub
⇔Witness = record
  { partIso = ⇔Witness'
  ; partIsoInt = ⇔WitnessInt
  }

