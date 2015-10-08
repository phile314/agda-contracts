{-# OPTIONS --type-in-type #-}

module Contracts.example where

open import Contracts.Isos

postulate dummy : forall {a} -> a
-- surface syntax tests
module T3 where
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


  
  -- an example how the contracts syntax could look like,
  -- if implemented using normal Agda constructs.
{-  ty' : AST
  ty' = ⟨ a ∷ ⟦ Set₁ ⟧ ⟩⇒
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
    ⟨ y ∷ ⟦ vec⇔list ⇋ lift a , ((lift x) , []) ⟧ ⟩⇒
    ⟨ xs ∷ ⟦ List a ⟧ ⟩⇒
    ⟨ ⟦ List a ⟧ ⟩-}


  open import Function
  open import Reflection as R
  open import Data.Unit
  
  f' : C
  f' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋  x , (wrap tt , wrap n) {-liftW x , liftW n , []-} ⟧ ⟩
  f : Term
  f = quoteTerm (makeContract
    (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x , ((wrap tt) , (wrap n)) {- liftW x , liftW n , []-} ⟧ ⟩))

  f-low : ℕ → (A : Set) → List A
  f-low n A = []
  
--  g : {!  f!}
--  g = {!getAgdaHighType (ast⇒T' f)!}
  g' : C
  g' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇏
    ⟨ x ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ f ∷ (⟨ _ ∷ ⟦ x ⟧ ⟩⇒ ⟨ ⟦ x ⟧ ⟩ ) ⟩⇒
    ⟨ _ ∷ ⟦ vec⇔list ⇋ x , ((wrap tt) , n) ⟧ ⟩⇒
    ⟨ ⟦ vec⇔list ⇋ x , ((wrap tt) , n) ⟧ ⟩

  open Reflect
  gg : unquote (deriveHighType (surface⇒internal f))
  gg = unquote (contract-apply (surface⇒internal f) (def (quote f-low) []))


  pp'' : _
  pp'' = assert (makeContract (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ x ⟧ ⟩)) dummy

  pp'4 : _
  pp'4 = assert (makeContract (⟨ ⟦ ℕ⇔ℤ ⇋ tt , ((wrap tt) , (wrap tt)) ⟧ ⟩)) dummy
  pp' : _
  pp' = assert (makeContract (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x , ((wrap tt) , (wrap n)) ⟧ ⟩)) f-low

  pp''' : _
  pp''' = assert (makeContract (⟨ _ ∷ ⟦ ℕ ⟧ ⟩⇏ ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x , ((wrap tt) , wrap n) ⟧ ⟩)) f-low


module Fmap where
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
        { ARGₐ = Set × Set
        ; ARGₗ = λ _ → ⊤
        ; ARGₕ = λ _ → ⊤
        ; τₗ = λ aa _ → List (proj₁ aa × proj₂ aa)
        ; τₕ = λ aa _ → Map (proj₁ aa) (proj₂ aa)
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

module MinusTest where
  open import Contracts.SSyn
  open import Contracts.Isos
  open import Data.Integer hiding (_≤_)
  open import Foreign.Base
  open NatIntIso
  open import Data.Nat

  minus' = foreign (hsCall "Prelude.-") (ℤ → ℤ → ℤ)

  -- not possible
{-  minus = assert (makeContract (
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩⇒
    ⟨ y ∷ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩⇒
    ⟨ _ ∷ ⟦ {!!} ⟧ ⟩⇏
    ⟨ ⟦ ℕ⇔ℤ ⇋ ∅ ⟧ ⟩)) minus'-}

module HigherOrderErasure where
  open import Contracts.SSyn
  open import Foreign.Base
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

open import IO
import IO.Primitive
open import Data.Unit
open import Data.Nat.Show
import Data.List
open import Data.Integer
open import Data.Nat

--open MapEx
--open DepCon1
open import Data.Vec

postulate exError : {A : Set} → A

{-
main : IO.Primitive.IO ⊤
main = run (putStrLn (Data.Nat.Show.show s))
  where n = 3
        p : Vec ℤ n
        p = + 0 ∷ (-[1+ 48 ] ∷ (+ 13 ∷ []))
        kk = myMap2 n ℤ ℕ (∣_∣) p

        s = foldl (λ _ → ℕ) Data.Nat._+_ 0 kk

-}

