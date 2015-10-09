{-# OPTIONS --type-in-type #-}

module Contracts.example where

-- surface syntax tests


open import Contracts.Isos
postulate dummy : forall {a} -> a


-- Some basic tests
module Basic where
  open NatIntIso
  open VecIso
  open import Contracts.Base
  open import Data.Nat as N
  open import Level
  open import Contracts.SSyn
  
  open import Data.List as List
  open import Data.Vec
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Data.Product


  open import Function
  open import Reflection as R
  open import Data.Unit
  
  f' : C
  f' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋  x , (wrap tt , wrap n) ⟧ ⟩
  f : Term
  f = quoteTerm (makeContract
    (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x , ((wrap tt) , (wrap n)) ⟧ ⟩))

  f-low : ℕ → (A : Set) → List A
  f-low n A = []
  

  open Reflect
  ff : unquote (deriveHighType (surface⇒internal f))
  ff = unquote (contract-apply (surface⇒internal f) (def (quote f-low) []))

  pp''' : _
  pp''' = assert (makeContract (⟨ _ ∷ ⟦ ℕ ⟧ ⟩⇏ ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x , ((wrap tt) , wrap n) ⟧ ⟩)) f-low



-- map example
module FMap where
  open import Data.List
  open import Contracts.SSyn
  open import Data.Nat
  open import Contracts.Isos
  open VecIso
  open import Contracts.Base
  open import Reflection
  open import Data.Product
  open import Data.Unit

  postulate
    hs-map : (A B : Set) → (A → B) → List A → List B


  map' = assert (makeContract (
    ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇏
    ⟨ A ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ B ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ f ∷ ⟨ _ ∷ ⟦ A ⟧ ⟩⇒ ⟨ ⟦ B ⟧ ⟩ ⟩⇒
    ⟨ _ ∷ ⟦ vec⇔list ⇋ ( A , (wrap tt , n) ) ⟧ ⟩⇒
    ⟨ ⟦ vec⇔list ⇋ B , (wrap tt , n) ⟧ ⟩)) hs-map

-- simple refined type example
module Witnessss where
  open import Contracts.Witness
  open import Contracts.SSyn
  open import Data.Nat
  open import Data.List
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Data.Unit hiding (_≟_)

  postulate f-low : ℕ → ℕ → ℕ

  f' : _ --ℕ → ℕ → Σ ℕ (_≡_ 10)
  f' = assert (makeContract (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ ⟦ ⇔Witness ⇋ (ℕ , (_≡_ 10 , _≟_ 10)) , wrap tt , wrap tt ⟧ ⟩)) f-low


-- test with partial isomorphism between [(a, b)] and a dummy Map a b type.
module TwoArgTest where
  open import Contracts.SSyn
  open import Contracts.Base
  open import Data.Unit
  open import Data.Product
  open import Data.List

  data Map (A B : Set) : Set where

  List⇔Map : PartIsoPub
  List⇔Map = makeIso partIso
    where
      partIso = record
        { ARG-a = Set × Set
        ; ARG-l = λ _ → ⊤
        ; ARG-h = λ _ → ⊤
        ; τ-l = λ aa _ → List (proj₁ aa × proj₂ aa)
        ; τ-h = λ aa _ → Map (proj₁ aa) (proj₂ aa)
        ; ⇅ = λ aa _ _ → dummy
        }

  f-low : (A B : Set) → List (A × B) → List (A × B)
  f-low = dummy
  f : _
  f = assert (makeContract (
    ⟨ A ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ B ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ _ ∷ ⟦ List⇔Map ⇋ (A , B) , (wrap tt) , (wrap tt) ⟧ ⟩⇒
    ⟨ ⟦ List⇔Map ⇋ (A , B) , (wrap tt) , (wrap tt) ⟧ ⟩)) f-low

-- Test with additional proof object using erasure annotations
module LookupTest where
  open import Contracts.SSyn
  open import Contracts.Isos
  open import Data.Nat
  open import Data.List

  postulate hs-lookup : (a : Set) → (n : ℕ) → List a → a

  lookup : _
  lookup = assert (makeContract (
    ⟨ a ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒
    ⟨ xs ∷ ⟦ List a ⟧ ⟩⇒
    ⟨ p ∷ ⟦ n ≤ length xs ⟧ ⟩⇏
    ⟨ ⟦ a ⟧ ⟩ )) hs-lookup

-- test with erased proof object depending on (partial) isomorphism application
module MinusTest where
  open import Contracts.SSyn
  open import Contracts.Isos
  open import Data.Integer hiding (_≤_)
  open NatIntIso
  open import Data.Nat

  postulate minus' : ℤ → ℤ → ℤ

  -- not possible
  {-
  minus = assert (makeContract (
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩⇒
    ⟨ y ∷ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩⇒
    ⟨ _ ∷ ⟦ {!!} ⟧ ⟩⇏
    ⟨ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩)) minus'
    -}

-- erasure in higher order functions
module HigherOrderErasure where
  open import Contracts.SSyn
  open import Data.Unit

  postulate foo' : (⊤ → ⊤) → ⊤

  open import Contracts.Base
  con = quoteTerm (makeContract (
    ⟨ _ ∷ ⟨ _ ∷ ⟦ ⊤ ⟧ ⟩⇏ ⟨ ⟦ ⊤ ⟧ ⟩ ⟩⇒
    ⟨ ⟦ ⊤ ⟧ ⟩
    ))

  foo = assert (makeContract (
    ⟨ _ ∷ ⟨ _ ∷ ⟦ ⊤ ⟧ ⟩⇏ ⟨ ⟦ ⊤ ⟧ ⟩ ⟩⇒
    ⟨ ⟦ ⊤ ⟧ ⟩
    )) foo'
