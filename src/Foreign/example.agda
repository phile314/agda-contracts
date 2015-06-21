module Foreign.example where

open import Foreign.Base

--open Foreign.Base.FunImport
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


module IdrisTest where
  open import Foreign.Base
  open Data
  open import Level
  open import Data.Maybe
  open import Reflection
  -- Problem: how do we handle foralls?
    -- a datatype may have foreign bindings to any number of FFIWays at the same time
  record ForeignData2 {l} (s : Set l) : Set l where
    field uhc-hs : (nm : Name) → Maybe (ForeignSpec UHC-HS nm)
--    field uhc-c  : Maybe (ForeignSpec UHC-C nm)

  data FFIDesc {l} : Set l → Set (Level.suc l) where
    Fun : {A : Set l} {B : Set l} → FFIDesc A → FFIDesc B → FFIDesc (A → B)
    Def : {A : Set l} → {{fd : ForeignData2 A}} → FFIDesc A

  open FunImport

--  derive : ∀ {a} {A : Set a} {f : FFIDesc A} → ForeignFun
--  derive {_} {_} {desc} = {!desc!}


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

  postulate IMPOSSIBLE : ∀ {a} → {A : Set a} → A

  open import Data.Nat
  tTy : Term → Set → Set
  tArgs : List (Arg Term) → Set → Set

  tTy (var x args) e = tArgs args e
  tTy (con c args) e = IMPOSSIBLE
  tTy (def f args) e = {{_ : ForeignData f}} → tArgs args e
  tTy (app t args) e = IMPOSSIBLE
  tTy (lam v t) e = IMPOSSIBLE
  tTy (pat-lam cs args) e = IMPOSSIBLE
--  tTy (pi (arg i (el s₁ (sort s))) (abs _ (el _ t₂))) e = tTy t₂ e
  tTy (pi (arg _ (el _ t₁)) (abs _ (el _ t₂))) e = tTy t₁ (tTy t₂ e)
  tTy (sort s) e = e
  tTy (lit l) e = IMPOSSIBLE
  tTy (quote-goal t) e = IMPOSSIBLE
  tTy (quote-term t) e = IMPOSSIBLE
  tTy quote-context e = IMPOSSIBLE
  tTy (unquote-term t args) e = IMPOSSIBLE
  tTy unknown e = IMPOSSIBLE

  tArgs [] e = e
  tArgs (arg i x ∷ xs) e = tTy x (tArgs xs e)

  τ : Set
  τ = τ-Hs UHC-HS

  open import Data.Maybe
  fromJust : {A : Set} → Maybe A → A
  fromJust (just x) = x
  fromJust nothing = IMPOSSIBLE -- error

  open import Data.List.NonEmpty
  
  der : {s : Set} → (t : Term) → (τ → s) → tTy t s
  das : {s : Set} → (xs : List (Arg Term)) → (τ → s) → τ → tArgs xs s

  der (var x args) e = das args e (var x)
  der (con c args) e = IMPOSSIBLE
  der (def f args) e = λ {{fd}} → das args e (ty f (fromJust (ForeignData.uhc-hs fd)))
  der (app t args) e = IMPOSSIBLE
  der (lam v t) e = IMPOSSIBLE
  der (pat-lam cs args) e = IMPOSSIBLE
  der (pi (arg i (el s₁ (sort s))) (abs _ (el _ t₂))) e = der t₂ (λ t₂' → e (∀' t₂'))
  der (pi (arg i (el s₁ t)) (abs s₂ (el s₃ t₁))) e = der t (λ t' → der t₁ (λ t₁' → e (t' ⇒ t₁')))
  der (sort s) e = IMPOSSIBLE
  der (lit l) e = IMPOSSIBLE
  der (quote-goal t) e = IMPOSSIBLE
  der (quote-term t) e = IMPOSSIBLE
  der quote-context e = IMPOSSIBLE
  der (unquote-term t args) e = IMPOSSIBLE
  der unknown e = IMPOSSIBLE
  
  das [] e τ = e τ
  das (arg i x ∷ xs) e τ = der x (λ x' → das xs e (app τ x'))

  die : {s : Set} → (t : Term) → (τ → s) → tTy t s
  die t cont = der t cont

  open import Data.Nat
  open import Data.Integer

  instance
    ℤ-FD : Data.ForeignData (quote ℤ)
    ℤ-FD = record { uhc-hs = just (Data.UHC-HS "Data.List" (quote ℤ)) ; uhc-c = nothing }
    ℕ-FD : Data.ForeignData (quote ℕ)
    ℕ-FD = record { uhc-hs = just (Data.UHC-HS "Data.List" (quote ℕ)) ; uhc-c = nothing }
    
  ex1 : Term
  ex1 = quoteTerm ({a : Set} → (a → a) → (List a → List a))-- (ℕ → (ℤ → ℕ) → ℕ) -- (ℕ → (ℤ → ℕ) → ℕ)

--  l : {!tTy ex1 τ!}
--  l = {!!}

  open Foreign.Base.HS
  open import Data.Bool

  derive : {s : Set} → (t : Term) → (τ → s) → tTy t s
  derive = die

{-  ex1' : τ -- tTy ex1 τ -- {!tTy ex1 (τ-Hs UHC-HS)!}
--  ex1' = λ {{a}} {{b}} → die ex1 {{a}} {{b}} --die ex1 -- die ex1  -- {!die ex1!}
  ex1' = {!!} --die ex1 -- appInst (die ex1)

  ex1'' : τ
  ex1'' = ex1'

--  q : {!tTy ex1 τ!}
--  q = {!definition (quote ex1')!}

  f : Term → Set
  f t = {{fd : Data.ForeignData (quote ℤ)}} → Term

  ex2 : (t : Term) → f t
  ex2 t {{fd}} = {!die ex1!}

  ex3 : Term → Term
  ex3 t = ex2 t-}


open ReflTest
open Foreign.Base.Data
open Foreign.Base.HS
open Foreign.Base.FunImport
open import Reflection
open import Data.Maybe

mkUhcHs : UHC-HS-EntityName → (t : Term) → tTy t ForeignFun
mkUhcHs unm t = die t (λ x → (record { uhc-native = just (UHC-HS unm x) }))

mkUhcC : UHC-C-EntityName → C-Safety → (t : Term) → tTy t ForeignFun
mkUhcC cnm cs t = die t (λ x → record { uhc-native = just (UHC-C cnm cs) })

--fdesc : ForeignFun
--fdesc = mkHsUhc "UHC.Agda.Builtins.primHsAdd" (quoteTerm (HSInteger → HSInteger → HSInteger))

add : HSInteger → HSInteger → HSInteger
--  using foreign fdesc
--  using foreign (mkHsUhc "UHC.Agda.Builtins.primHsAdd" (quoteTerm (HSInteger → HSInteger → HSInteger)))
  using foreign (mkUhcHs "UHC.Agda.Builtins.primHsAdd")

postulate CInt : Set

--addC : CInt → CInt → CInt
--  using foreign (mkUhcC "math.h add" safe)

{-
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
-}
