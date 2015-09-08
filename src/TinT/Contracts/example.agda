{-# OPTIONS --type-in-type #-}

module Contracts.example where

open import Contracts.Isos

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
  
  f' : AST
  f' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ liftW x , liftW n , [] ⟧ ⟩
  f : Term
  f = quoteTerm (makeContract (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ liftW x , liftW n , [] ⟧ ⟩))

  f-low : ℕ → (A : Set) → List A
  f-low n A = []
  
--  g : {!  f!}
--  g = {!getAgdaHighType (ast⇒T' f)!}
  g' : AST
  g' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇏
    ⟨ x ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ f ∷ (⟨ _ ∷ ⟦ x ⟧ ⟩⇒ ⟨ ⟦ x ⟧ ⟩ ) ⟩⇒
    ⟨ _ ∷ ⟦ vec⇔list ⇋ (liftW x) , (n , []) ⟧ ⟩⇒
    ⟨ ⟦ vec⇔list ⇋ (liftW x) , (n , []) ⟧ ⟩

--  gg : unquote (getAgdaHighType (ast⇒T' f))
--  gg = unquote (ffi-lift (ast⇒T' f) (def (quote f-low) []))

  ggg : {!pretty (getAgdaLowType (ast⇒T' {0} (quoteTerm (makeContract (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x ,, n ,, [] ⟧ ⟩)))))!}
  ggg = {!lett (var 10 []) inn var 0 []!}

  pp'' : _
  pp'' = assert (makeContract (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ x ⟧ ⟩)) error

  pp'4 : _
  pp'4 = assert (makeContract (⟨ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩)) error
  pp' : _
  pp' = assert (makeContract (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x ,, n ,, [] ⟧ ⟩)) f-low

  pp''' : _
  pp''' = assert (makeContract (⟨ _ ∷ ⟦ ℕ ⟧ ⟩⇏ ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x ,, n ,, [] ⟧ ⟩)) f-low

  {-
  open import Data.Integer
  addImpl' : ℤ → ℤ → ℤ
  addImpl' a b = a Data.Integer.+ b

  addContr : Term
  addContr = quoteTerm (
        ⟨ a ∷ ⟦ ℤ ⟧ ⟩⇒ --⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
        ⟨ b ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
        ⟨ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩ )
--        ⟨ ⟦ vec⇔list ⇋ lift ℕ , lift n , [] ⟧ ⟩ )

--  add : unquote (getAgdaHighType (ast⇒T' addContr))
--  add = unquote (ffi-lift (ast⇒T' addContr) (quote addImpl'))


  
  open import Data.Bool
  lk : Bool → Term
  lk true = let x = {!open import Data.List!} in {!!}
  lk false = {!add ( -[1+ 30 ] ) (24)!}
    where open import Data.List public

  postulate mkForeign : {a : Set} → a
-}
--  q : ℕ → ℕ
--  q = tactic t

--  q' : ℕ → ℕ
--  q' = quoteGoal g in unquote {!g!}

--  r : ℕ → ℕ
--    using foreign (record {})

module Map where
  open import Data.List
  open import Contracts.SSyn
  open import Data.Nat
  open import Contracts.Isos
  open VecIso
  open import Contracts.Base
  open import Reflection

  postulate
    hs-map : ℕ → (A : Set) → {- (A → A)-} (ℕ → ℕ) → List A --→ List A

  g : {!!}
  g = {!unquote (ffi-lift (ast⇒T' {0} (quoteTerm (makeContract (
    ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ --⇏
    ⟨ A ∷ ⟦ Set ⟧ ⟩⇒
--    ⟨ f ∷ ⟨ _ ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ ⟦ ℕ ⟧ ⟩ ⟩⇒
--    ⟨ _ ∷ ⟦ vec⇔list ⇋ ( A ,, (n , []) ) ⟧ ⟩⇒
    ⟨ ⟦ vec⇔list ⇋ A ,, (3 ,, []) ⟧ ⟩)))) (def (quote hs-map) []) )!}
{-  map' : _
  map' = assert (makeContract (
    ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇏
    ⟨ A ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ f ∷ ⟨ _ ∷ ⟦ A ⟧ ⟩⇒ ⟨ ⟦ A ⟧ ⟩ ⟩⇒
    ⟨ _ ∷ ⟦ vec⇔list ⇋ ( A ,, (n , []) ) ⟧ ⟩⇒
    ⟨ ⟦ vec⇔list ⇋ A ,, (n , []) ⟧ ⟩)) hs-map-}

module Witnessss where
  open import Contracts.Witness
  open import Contracts.SSyn
  open import Data.Nat
  open import Data.List

  postulate f-low : ℕ → ℕ → ℕ

--  f' : _
--  f' = assert (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ (⇔Witness (_≟_ 10)) ⇋ {!!} ⟧ ⟩) f-low

open import IO
import IO.Primitive
open import Data.Unit
open import Data.Nat.Show
import Data.List
open import Data.Integer
open import Data.Nat

--open MapEx
open DepCon1
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
