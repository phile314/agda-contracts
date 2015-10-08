module Foreign.Base where

open import Data.String
open import Reflection

-- Some type synonyms
JSCode : Set
JSCode = String

HSCode : Set
HSCode = String

UHC-Core-Expr UHC-HS-Name : Set
UHC-Core-Expr = String
UHC-HS-Name = String

-- Describes a function import.
data FunImport : Set where
  MAZ-HS : HSCode -> FunImport
  JS-JS : JSCode -> FunImport
  -- UHC Core import. Doesn't do any Set/Level magic.
  UHC-Core : UHC-Core-Expr -> FunImport
  -- UHC HS import. Handles Set/Level arguments automatically.
  UHC-HS : UHC-HS-Name -> FunImport
  -- Just fail at runtime.
  RuntimeError : FunImport
{-# BUILTIN FFIFUNIMPORT FunImport #-}
{-# BUILTIN FFIFUNIMPORTMAZHS MAZ-HS #-}
{-# BUILTIN FFIFUNIMPORTJSJS  JS-JS #-}
{-# BUILTIN FFIFUNIMPORTUHCCORE UHC-Core #-}
{-# BUILTIN FFIFUNIMPORTUHCHS UHC-HS #-}
{-# BUILTIN FFIFUNIMPORTRUNTIMEERROR RuntimeError #-}

-- Contains the FFI function import for each compile target.
record FunImportSpec : Set where
  constructor FFICall
  field
    Spec-MAZ-Native Spec-JS-JS Spec-UHC-Native : FunImport
{-# BUILTIN FFIFUNIMPORTSPEC FunImportSpec #-}

-- Creates a Haskell call for UHC.
hsCall : UHC-HS-Name -> FunImportSpec
hsCall nm = record
  { Spec-MAZ-Native = RuntimeError
  ; Spec-JS-JS = RuntimeError
  ; Spec-UHC-Native = UHC-HS nm
  }
