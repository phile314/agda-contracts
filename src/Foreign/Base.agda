module Foreign.Base where

open import Data.String
open import Reflection using (Name; showName)

data CompileTarget : Set where
  UHC-Native : CompileTarget -- producing executables
-- {-# BUILTIN COMPILETARGET CompileTarget #-}
-- {-# BUILTIN COMPILETARGETUHCNATIVE UHC-Native #-}

data FFIWay : CompileTarget → Set where
  UHC-HS : FFIWay UHC-Native
  UHC-C  : FFIWay UHC-Native
-- {-# BUILTIN FFIWAY FFIWay #-}
-- {-# BUILTIN FFIWAYUHCHS UHC-HS #-}
-- {-# BUILTIN FFIWAYUHCC UHC-C #-}

UHC-CR-Expr UHC-HS-Name : Set
UHC-CR-Expr = String
UHC-HS-Name = String


{-
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

-}

module FunImport where

{-
  data C-Safety : Set where
    safe : C-Safety
    unsafe : C-Safety
  {-# BUILTIN FFICSAFETY C-Safety #-}
  {-# BUILTIN FFICSAFETYSAFE safe #-}
  {-# BUILTIN FFICSAFETYUNSAFE unsafe #-}

  open import Data.Nat
  open import Data.Fin
-}



  data UHCFunImport : Set where
    HS : UHC-HS-Name -> UHCFunImport
    Core : UHC-CR-Expr -> UHCFunImport
  {-# BUILTIN FFIUHCFUNIMPORT UHCFunImport #-}
  {-# BUILTIN FFIUHCFUNIMPORTHS HS #-}
  {-# BUILTIN FFIUHCFUNIMPORTCORE Core #-}

  data CallSpec : Set -> Set where
    CompileError : forall {A} -> CallSpec A
    RuntimeError : forall {A} -> CallSpec A
    Spec : forall {A} -> A -> CallSpec A
  {-# BUILTIN FFICALLSPEC CallSpec #-}
  {-# BUILTIN FFICALLSPECCOMPILEERROR CompileError #-}
  {-# BUILTIN FFICALLSPECRUNTIMEERROR RuntimeError #-}
  {-# BUILTIN FFICALLSPECSPEC Spec #-}


  data FFICall : Set where
    Call : CallSpec UHCFunImport -> FFICall
  {-# BUILTIN FFICALL FFICall #-}
  {-# BUILTIN FFICALLCALL Call #-}
