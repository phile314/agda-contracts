module Foreign.Base where

open import Level
open import Data.String
open import Reflection using (Name; showName)

data CompileTarget : Set where
  UHC-Native : CompileTarget -- producing executables
{-# BUILTIN COMPILETARGET CompileTarget #-}
{-# BUILTIN COMPILETARGETUHCNATIVE UHC-Native #-}

data FFIWay : CompileTarget → Set where
  UHC-HS : FFIWay UHC-Native
  UHC-C  : FFIWay UHC-Native
{-# BUILTIN FFIWAY FFIWay #-}
{-# BUILTIN FFIWAYUHCHS UHC-HS #-}
{-# BUILTIN FFIWAYUHCC UHC-C #-}

UHC-C-EntityName : Set
UHC-C-EntityName = String

UHC-HS-EntityName : Set
UHC-HS-EntityName = String

AGDA-EntityName : Set
AGDA-EntityName = Name


module Data where

  open import Data.Maybe

  -- the mapping is not stored inside the ForeignSpec,
  -- the ForeignData is just used to servce as proof object.
  -- The user is not expected to create ForeignSpec objects by hand!
  -- Assumption: If a ForeignSpec object exists, it is assumed
  -- that all the constituents of the given object can be passed through
  -- the FFI. The checking that this is possible should be done
  -- at the location where the ForeignSpec is declared.
  data ForeignSpec : {ct : CompileTarget} → FFIWay ct → AGDA-EntityName → Set where
    UHC-HS : UHC-HS-EntityName -- name is only used for debugging
      → (nm : AGDA-EntityName)
      → ForeignSpec UHC-HS nm
    UHC-C : UHC-C-EntityName
      → (nm : AGDA-EntityName)
      → ForeignSpec UHC-C nm
  {-# BUILTIN FFIDATASPEC ForeignSpec #-}
  {-# BUILTIN FFIDATASPECUHCHS UHC-HS #-}
  {-# BUILTIN FFIDATASPECUHCC UHC-C #-}

  -- a datatype may have foreign bindings to any number of FFIWays at the same time
  record ForeignData (nm : Name) : Set where
    field uhc-hs : Maybe (ForeignSpec UHC-HS nm)
    field uhc-c  : Maybe (ForeignSpec UHC-C nm)
  {-# BUILTIN FFIDATADATA ForeignData #-}


module FunImport where

  data C-Safety : Set where
    safe : C-Safety
    unsafe : C-Safety
  {-# BUILTIN FFICSAFETY C-Safety #-}
  {-# BUILTIN FFICSAFETYSAFE safe #-}
  {-# BUILTIN FFICSAFETYUNSAFE unsafe #-}

  open import Data.Nat
  open import Data.Fin


  -- The grammar of Haskell types, using de-bruijn indices.
  data τ-Hs : {ct : CompileTarget} → (way : FFIWay ct) → Set where --: {ct : CompileTarget} (way : FFIWay ct) → Set where
    var : ∀ {ct} → {way : FFIWay ct} → (k : ℕ) → τ-Hs way
    app : ∀ {ct} → {way : FFIWay ct} → τ-Hs way → τ-Hs way → τ-Hs way
    ∀'  : ∀ {ct} → {way : FFIWay ct} → τ-Hs way → τ-Hs way
    _⇒_ : ∀ {ct} → {way : FFIWay ct} → τ-Hs way → τ-Hs way → τ-Hs way
    ty  : ∀ {ct} → {way : FFIWay ct} → (nm-Agda : Name) → (foreign-data : Data.ForeignSpec way nm-Agda) → τ-Hs way
  {-# BUILTIN FFIHSTY τ-Hs #-}
  {-# BUILTIN FFIHSTYVAR var #-}
  {-# BUILTIN FFIHSTYAPP app #-}
  {-# BUILTIN FFIHSTYFORALL ∀' #-}
  {-# BUILTIN FFIHSTYFUN _⇒_ #-}
  {-# BUILTIN FFIHSTYDATA ty #-}

  data ForeignSpec : CompileTarget → Set where
    UHC-HS : UHC-HS-EntityName → τ-Hs UHC-HS → ForeignSpec UHC-Native
    UHC-C : UHC-C-EntityName → C-Safety → ForeignSpec UHC-Native -- c type descriptor is missing!
  {-# BUILTIN FFIFUNSPEC ForeignSpec #-}
  {-# BUILTIN FFIFUNSPECUHCHS UHC-HS #-}
  {-# BUILTIN FFIFUNSPECUHCC UHC-C #-}

  open import Data.Maybe

  -- there must be at most one binding for each compile target
  record ForeignFun : Set where
    field uhc-native : Maybe (ForeignSpec UHC-Native)
  {-# BUILTIN FFIFUNFUN ForeignFun #-}

  open import Data.List using (List; foldl)
  apps : ∀ {ct} → {way : FFIWay ct} → τ-Hs way → List (τ-Hs way) → τ-Hs way
  apps f xs = foldl app f xs




module HS where
  open import Data.List
  open import Reflection
  open import Data.Maybe
  open Data
  postulate
    HSInteger : Set
    HSInt : Set
    HSDouble : Set
  instance
    HSInteger-FD : Data.ForeignData (quote HSInteger)
    HSInteger-FD = record { uhc-hs = just (Data.UHC-HS "Data.List" (quote HSInteger)) ; uhc-c = nothing }

  HSList : ∀ {l} → Set l → Set l
  HSList = Data.List.List

  

