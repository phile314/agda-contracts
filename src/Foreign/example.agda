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

  derive : ∀ {a} {A : Set a} {f : FFIDesc A} → ForeignFun
  derive {_} {_} {desc} = {!desc!}


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

  tTy : Term → Set → Set
  tArgs : List (Arg Term) → Set → Set

  tTy (var x args) e = tArgs args e
  tTy (con c args) e = IMPOSSIBLE
  tTy (def f args) e = {{ fd : ForeignData f }} → tArgs args e
  tTy (app t args) e = IMPOSSIBLE
  tTy (lam v t) e = IMPOSSIBLE
  tTy (pat-lam cs args) e = IMPOSSIBLE
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
  fromJust = {!!}

  open import Data.List.NonEmpty
  
  der : (t : Term) → (s : Set) → (τ → s) {- (k : τ → s)-} → tTy t s
  das : (xs : List (Arg Term)) → (s : Set) → (τ → s) → τ → tArgs xs s
--  das : (xs : List⁺ (Arg Term)) → (s : Set) (k : τ)  → tArgs (toList xs) s
--  buildFun : (args : List (Arg Term)) → tArgs args

  der (var x args) s e = das args s e (var x)
  der (con c args) e = IMPOSSIBLE
  der (def f args) s e = λ {{fd}} → das args s e (ty f {!!}) -- {!!} (das args {!!}) --das args s (ty f (fromJust (ForeignData.uhc-hs fd))) --(ty f (fromJust (ForeignData.uhc-hs fd)))
  der (app t args) e = {!!}
  der (lam v t) e = {!!}
  der (pat-lam cs args) e = {!!}
  der (pi t₁ t₂) e = {!!}
  der (sort s) e = {!!}
  der (lit l) e = {!!}
  der (quote-goal t) e = {!!}
  der (quote-term t) e = {!!}
  der quote-context e = {!!}
  der (unquote-term t args) e = {!!}
  der unknown e = {!!}
  
  das [] s e τ = e τ
  das (arg i x ∷ xs) s e τ = der x (tArgs xs s) (λ x' → das xs s e (app τ x'))

  die : (t : Term) → tTy t τ
  die t = der t τ (λ x → x)

  open import Data.Nat
  open import Data.Integer
  ex1 : Term
  ex1 = quoteTerm (ℕ → (ℤ → ℕ) → ℕ)

  ex1' : {!tTy ex1 (τ-Hs UHC-HS)!}
  ex1' = {!!}

--  {-# TERMINATING #-}
{-  xTy : Term → List Name
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

  k : Term → Set → Set
  k t f = g ns
    where
      ns = xTy t
      g : List Name → Set
      g [] = f
      g (x ∷ xs) = {{ fd : ForeignData x}} → g xs

  xTy' : Term → Set
  xTy' t = g ns
    where
      ns = xTy t
      g : List Name → Set
      g [] = τ-Hs UHC-HS
      g (x ∷ xs) = {{ fd : ForeignData x }} → g xs

  xArgTy : List (Arg Term) → Set
  xArgTy [] = τ-Hs UHC-HS
  xArgTy ((arg _ x) ∷ xs) = k x (xArgTy xs)

  args : Term → Set
  args (var x args) = List (τ-Hs UHC-HS) -- the terms for the args
  args (con c args) = IMPOSSIBLE
  args (def f args) = List (τ-Hs UHC-HS) -- the terms for the args
  args (app t args) = IMPOSSIBLE
  args (lam v t) = IMPOSSIBLE
  args (pat-lam cs args) = IMPOSSIBLE
  args (pi t₁ t₂) = {!!}
  args (sort s) = {!!}
  args (lit l) = IMPOSSIBLE
  args (quote-goal t) = IMPOSSIBLE
  args (quote-term t) = IMPOSSIBLE
  args quote-context = IMPOSSIBLE
  args (unquote-term t args) = IMPOSSIBLE
  args unknown = IMPOSSIBLE

  x : (t : Term)
--    → (args t → τ-Hs UHC-HS)
    → xTy' t
  y : (args : List (Arg Term))
    → τ-Hs UHC-HS -- function
    → xArgTy args

  x (var x args) = {!!}
  x (con c args) = IMPOSSIBLE
  x (def f args) = λ {{fd}} → y args {!!} -- τ-Hs.ty f (ForeignData.foreign-spec fd) --(τ-Hs.ty {!τ-Hs.ty!} )
  x (app t args) = IMPOSSIBLE
  x (lam v t) = IMPOSSIBLE
  x (pat-lam cs args) = IMPOSSIBLE
  x (pi (arg i (el s (sort s₁))) (abs s₂ x)) = {!!} -- forall
  x (pi (arg i (el s t)) (abs s₁ x)) = {!!} -- recurse into both
  x (sort s) = {!!}
  x (lit l) = IMPOSSIBLE
  x (quote-goal t) = IMPOSSIBLE
  x (quote-term t) = IMPOSSIBLE
  x quote-context = IMPOSSIBLE
  x (unquote-term t args) = IMPOSSIBLE
  x unknown = IMPOSSIBLE
--  x _ = {!!}

  y = {!!}

  open import Data.Nat
  open import Data.Integer
  open Foreign.Base.HS
  l : Set
  l = ℤ

  m : τ-Hs UHC-HS
  m = x (quoteTerm HSInteger)-}

--  y : {!quoteTerm ( { a : Set} → a )!}
--  y = {!!}



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
