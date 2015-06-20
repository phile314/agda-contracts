module Foreign.example where

open import Foreign.Base

open Foreign.Base.FunImport
{-
module Ta where
  open import Data.List
  open import Reflection

  postulate notImpl : {A : Set} → A

  wayArg : Arg Term
  wayArg = (arg (arg-info hidden relevant) (quoteTerm FFIWay.UHC-HS))

  

  fromTy : List Term → Term → Term
  fromTy env (var x []) = con (quote τ-Hs.var) (wayArg
         ∷ arg (arg-info visible relevant) (lit (nat x))
         ∷ [])
  fromTy env (con c args) = {!!}
  fromTy env (def f args) = def (quote ty) (wayArg
         ∷ {!!}
         ∷ {!!}
         ∷ [])
  fromTy env (app t args) = {!!}
  fromTy env (lam v t) = {!!}
  fromTy env (pat-lam cs args) = {!!}
  fromTy env (pi (arg i (el s t)) (abs s₁ (el _ x₁))) = con (quote _⇒_) (wayArg
         ∷ arg (arg-info visible relevant) (fromTy env t)
         ∷ arg (arg-info visible relevant) (fromTy env x₁)
         ∷ [])
  fromTy env (sort s) = {!!}
  fromTy env (lit l) = {!!}
  fromTy env (quote-goal t) = {!!}
  fromTy env (quote-term t) = {!!}
  fromTy env quote-context = {!!}
  fromTy env (unquote-term t args) = {!!}
  fromTy env unknown = {!!}
  fromTy _ _ = notImpl
-}

module Ex1 where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  {-# COMPILED_DATA_UHC List __LIST__ __NIL__ __CONS__ #-}

  open import Data.Maybe
  blub : Data.ForeignData (quote List)
  blub = record { uhc-hs = just (Data.UHC-HS "Data.List.List" (quote List)) ; uhc-c = nothing }


--  head : ∀ {a} → List a → a
--    using foreign (record { foreign-spec = (HS-UHC "Prelude.head" (∀' (( ty (quote List) (Data.ForeignData.foreign-spec blub) ) ⇒ (var 0)) )) } )

module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Data.Maybe
  open import Data.Product
  open import Data.List
  open Foreign.Base.HS
  import Level

{-  instance
    bla : Data.ForeignData (quote ℤ)
    bla = record { foreign-spec = Data.HS-UHC "Integer" (quote ℤ)}-}

  postulate
    ℤ⇒HSInteger : ℤ → HSInteger
    HSInteger⇒ℤ : HSInteger → ℤ
  {-# COMPILED_UHC ℤ⇒HSInteger UHC.Agda.Builtins.primAgdaIntegerToHsInteger #-}
  {-# COMPILED_UHC HSInteger⇒ℤ UHC.Agda.Builtins.primHsIntegerToAgdaInteger #-}

open Foreign.Base.HS
open Ex2
open import Data.Maybe
import Foreign.Base
open Foreign.Base.Data

postulate err : {A : Set} → A
fromJust : {A : Set} → Maybe A → A
fromJust (just x) = x
fromJust nothing = err


hsIntTy : τ-Hs UHC-HS
hsIntTy = ty (quote HSInteger) (fromJust (ForeignData.uhc-hs HSInteger-FD))

add : HSInteger → HSInteger → HSInteger
  using foreign (record { uhc-native = just (UHC-HS "UHC.Agda.Builtins.primHsAdd" (hsIntTy ⇒ (hsIntTy ⇒ hsIntTy))) } )

import IO.Primitive
open import IO
open import Data.Unit
open import Data.Integer
main : IO.Primitive.IO ⊤
main = run (putStrLn (Data.Integer.show (HSInteger⇒ℤ (add (ℤ⇒HSInteger (+ 32)) (ℤ⇒HSInteger (+ 54))))))

{-
-- test if we can use instance args with reflection.
-- Solution: Produce a function which takes instance arguments
module ReflTest where

  open import Reflection
  open import Data.List
  open import Foreign.Base
  open Foreign.Base.Data
  open Foreign.Base.FunImport
  open import Function

  unArg : Arg Term → Term
  unArg (arg i x) = x

  postulate IMPOSSIBLE : {A : Set} → A

  {-# TERMINATING #-}
  xTy : Term → List Name
  xTy (var x args) = concat (map (xTy ∘ unArg) args)
  xTy (con c args) = IMPOSSIBLE
  xTy (def f args) =  f ∷ (concat (map (xTy ∘ unArg) args))
  xTy (app t args) = IMPOSSIBLE
  xTy (lam v t) = IMPOSSIBLE -- can this actually happen? Anyway, Haskell doesn't supprt lambdas in types, so just fail
  xTy (pat-lam cs args) = IMPOSSIBLE
  xTy (pi (arg i (el s t)) (abs s₁ (el s₂ t₁))) = xTy t ++ xTy t₁
  xTy (sort s) = []
  xTy (lit l) = IMPOSSIBLE
  xTy (quote-goal t) = IMPOSSIBLE
  xTy (quote-term t) = IMPOSSIBLE
  xTy quote-context = IMPOSSIBLE
  xTy (unquote-term t args) = IMPOSSIBLE
  xTy unknown = IMPOSSIBLE

  xTy' : Term → Set
  xTy' t = g ns
    where
      ns = xTy t
      g : List Name → Set
      g [] = τ-Hs UHC-HS
      g (x ∷ xs) = {{ fd : ForeignData x }} → g xs

  x : (t : Term) → xTy' t
  x (var x args) = {!!}
  x (con c args) = IMPOSSIBLE
  x (def f args) = λ {{fd}} → {!!} -- τ-Hs.ty f (ForeignData.foreign-spec fd) --(τ-Hs.ty {!τ-Hs.ty!} )
  x (app t args) = IMPOSSIBLE
  x (lam v t) = IMPOSSIBLE
  x (pat-lam cs args) = IMPOSSIBLE
  x (pi (arg i x) t₂) = {!!} -- here we need to check if t₁ is of type set.
  x (sort s) = {!!}
  x (lit l) = IMPOSSIBLE
  x (quote-goal t) = IMPOSSIBLE
  x (quote-term t) = IMPOSSIBLE
  x quote-context = IMPOSSIBLE
  x (unquote-term t args) = IMPOSSIBLE
  x unknown = IMPOSSIBLE
--  x _ = {!!}

  open import Data.Nat
  open import Data.Integer
  open Foreign.Base.HS
  k : Set
  k = ℤ

  m : τ-Hs UHC-HS
  m = x (quoteTerm HSInteger)

  y : {!quoteTerm ( { a : Set} → a )!}
  y = {!!}
-}
