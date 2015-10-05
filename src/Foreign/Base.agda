module Foreign.Base where

open import Data.String
open import Reflection

JSCode : Set
JSCode = String

HSCode : Set
HSCode = String

UHC-Core-Expr UHC-HS-Name : Set
UHC-Core-Expr = String
UHC-HS-Name = String


data FunImport : Set where
  MAZ-HS : HSCode -> FunImport
  JS-JS : JSCode -> FunImport
  UHC-Core : UHC-HS-Name -> FunImport
  UHC-HS : UHC-HS-Name -> FunImport
  RuntimeError : FunImport
--  UHC-Core : UHC-Core-Expr -> FunImport
{-# BUILTIN FFIFUNIMPORT FunImport #-}
{-# BUILTIN FFIFUNIMPORTMAZHS MAZ-HS #-}
{-# BUILTIN FFIFUNIMPORTJSJS  JS-JS #-}
{-# BUILTIN FFIFUNIMPORTUHCCORE UHC-Core #-}
{-# BUILTIN FFIFUNIMPORTUHCHS UHC-HS #-}
{-# BUILTIN FFIFUNIMPORTRUNTIMEERROR RuntimeError #-}


record FunImportSpec : Set where
  constructor FFICall
  field
    Spec-MAZ-Native Spec-JS-JS Spec-UHC-Native : FunImport
{-# BUILTIN FFIFUNIMPORTSPEC FunImportSpec #-}

hsCall : UHC-HS-Name -> FunImportSpec
hsCall nm = record
  { Spec-MAZ-Native = RuntimeError
  ; Spec-JS-JS = RuntimeError
  ; Spec-UHC-Native = UHC-HS nm
  }
