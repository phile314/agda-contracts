module Foreign.Base where

open import Level
open import Data.String
open import Reflection using (Name; showName)

data FFIWay : Set where
  HS-UHC : FFIWay
{-# BUILTIN FFIWAY FFIWay #-}
{-# BUILTIN FFIWAYHSUHC HS-UHC #-}

HS-UHC-EntityName : Set
HS-UHC-EntityName = String

AGDA-EntityName : Set
AGDA-EntityName = Name

module Data where

  -- the mapping is not stored inside the ForeignSpec,
  -- the ForeignData is just used to servce as proof object.
  data ForeignSpec : FFIWay → AGDA-EntityName → Set where
    HS-UHC : HS-UHC-EntityName -- name is only used for debugging
      → (nm : AGDA-EntityName)
      → ForeignSpec HS-UHC nm
  {-# BUILTIN FFIDATASPEC ForeignSpec #-}
  {-# BUILTIN FFIDATASPECHSUHC HS-UHC #-}

  record ForeignData (nm : Name) : Set where
    -- TODO allow more than one FFI spec, eg List of Spec
    field foreign-spec : ForeignSpec HS-UHC nm
  {-# BUILTIN FFIDATADATA ForeignData #-}

module Fun where

  open import Data.Nat
  open import Data.Fin
  -- The grammar of Haskell types, using de-bruijn indices.
  data τ-Hs : (way : FFIWay) → Set where
    var : ∀ {way} → (k : ℕ) → τ-Hs way
    app : ∀ {way} → τ-Hs way → τ-Hs way → τ-Hs way
    ∀'  : ∀ {way} → τ-Hs way → τ-Hs way
    _⇒_ : ∀ {way} → τ-Hs way → τ-Hs way → τ-Hs way
    ty  : ∀ {way} → (nm-Agda : Name) → (foreign-data : Data.ForeignSpec way nm-Agda) → τ-Hs way
  {-# BUILTIN FFIHSTY τ-Hs #-}
  {-# BUILTIN FFIHSTYVAR var #-}
  {-# BUILTIN FFIHSTYAPP app #-}
  {-# BUILTIN FFIHSTYFORALL ∀' #-}
  {-# BUILTIN FFIHSTYFUN _⇒_ #-}
  {-# BUILTIN FFIHSTYDATA ty #-}

  data ForeignSpec : FFIWay → Set where
    HS-UHC : HS-UHC-EntityName → τ-Hs HS-UHC → ForeignSpec HS-UHC
  {-# BUILTIN FFIFUNSPEC ForeignSpec #-}
  {-# BUILTIN FFIFUNSPECHSUHC HS-UHC #-}

  record ForeignFun : Set where
    -- TODO multi ffi specs
    field foreign-spec : ForeignSpec HS-UHC
  {-# BUILTIN FFIFUNFUN ForeignFun #-}

  open import Data.List using (List; foldl)
  apps : ∀ {way} → τ-Hs way → List (τ-Hs way) → τ-Hs way
  apps f xs = foldl app f xs



