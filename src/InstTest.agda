module InstTest where

open import Foreign.Base

open FunImport
open HS
open Data
open import Data.Maybe

open import Foreign.example

mkDesc : {{fd : ForeignData (quote HSInteger)}} → ForeignFun
mkDesc {{fd}} = record { uhc-native = just (UHC-HS "sdf" (var 0)) }

fdesc2 : ForeignFun
fdesc2 = mkDesc

open import Data.Char

k : HSInteger
--  using foreign fdesc
--  using foreign mkDesc
  using foreign (mkUhcHs "UHC.Agda.Builtins.primHsAdd")


open import Reflection
open import Data.List
test : {{fd : ForeignData (quote HSInteger)}} → Term
test {{fd}} = def (quote test) []

--test2 : HSInteger
--test2 = quoteGoal g in {!g!}
