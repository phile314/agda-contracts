{-# OPTIONS --type-in-type #-}
module Contracts.Witness where

open import Contracts.Base
open import Relation.Nullary
open import Data.List
open import Data.Product
open import Function
open import Data.Maybe

{-
⇔Witness' : {A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → PartIso
⇔Witness' {A} {B} d = record
  { ARGₐ = [] ; HIGHₐ = [] ; iso = A , ((Σ A B) , conv) }
  where
    -- we can't provide a (A → Dec (Σ A B)) here, because
    -- this would mean we have to prove that there is no
    -- such pair for all possible values of A.
    -- Using withMaybe works fine though.
    w-up : A → Maybe (Σ A B)
    w-up a = case d a of λ
      { (yes p) → just (a , p)
      ; (no ¬p) → nothing }
    conv = (withMaybe w-up) , (total proj₁)
-}
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


open import Reflection

⇔WitnessInt : PartIsoInt
⇔WitnessInt = record { wrapped = def (quote ⇔Witness') [] }

open import Contracts.SSyn

⇔Witness : PartIsoPub
⇔Witness = record
  { partIso = ⇔Witness'
  ; partIsoInt = ⇔WitnessInt
  }

{-
⇔Witness :{A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → PartIsoPub
⇔Witness dec = record
  { partIso = ⇔Witness' dec
  ; partIsoInt = record
    { wrapped = quoteTerm (⇔Witness' dec) }
  }
-}

open import Contracts.SSyn

{-⇔Witness : {A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → PartIsoPub
⇔Witness d = mkIsoPub (⇔Witness' d) (mkIsoInt {!!})
-}

{-
open import Reflection
open import Contracts.SSyn
macro
--  ⇔Witness : {A : Set} {B : A → Set} → ((a : A) → Dec (B a)) → PartIsoPub
  -- dec -> partiso
  ⇔Witness : Term {- base type-} → Term {- witness type -} → Term → Term
  ⇔Witness lty hty dec = con (quote mkIsoPub) (arg (arg-info visible relevant) (pi') ∷ arg (arg-info visible relevant) pii ∷ [])
    where
      -- part iso
      pi' = def (quote ⇔Witness') (arg (arg-info hidden relevant) lty
        ∷ arg (arg-info hidden relevant) hty
        ∷ arg (arg-info visible relevant) dec ∷ [])
      -- part iso int
      pii = con (quote mkIsoInt) [ arg (arg-info visible relevant)
        -- this has to be a term, describing how to build the PartIso
        (quote-term (pi')) ]
--        (def (quote def) {!⇔Witness'!}) ]
        --(def (quote _$_) (arg def-argInfo (def (quote ⇔Witness') []) ∷ arg def-argInfo dec ∷ [])) ]

-}
open import Data.Nat

dec : Term
dec = quoteTerm (Data.Nat._≟_ 10)

open import Relation.Binary.PropositionalEquality

--g : {!unquote (def (quote ⇔Witness') (arg (arg-info visible relevant) dec ∷ []))!}
--g = {!quoteTerm ((makeContract (⟨ ⟦ ⇔Witness2 ⇋ (C (ℕ , ((_≡_ 10) , Data.Nat._≟_ 10))) , [] ⟧ ⟩ )))!}


--f : _ --Σ ℕ (λ x → 10 ≡ x)
--f = assert (makeContract (⟨ ⟦ ⇔Witness2 ⇋ (C (ℕ , ((_≡_ 10) , Data.Nat._≟_ 10))) , [] ⟧ ⟩ )) error
