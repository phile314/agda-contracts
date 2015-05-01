module FFI.PartIso.Core where

open import Level as L
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat
open import Data.List

data Conversion {a b} (A : Set a) (B : Set b) : Set (L.suc (a L.⊔ b)) where
  total : (A → B) → Conversion A B
  withDec : (A → Dec B) → Conversion A B
  withMaybe : (A → Maybe B) → Conversion A B
  fail : Conversion A B

data ArgTys {c} : Set (L.suc c) where
  [] : ArgTys {c}
  _∷_ : (A : Set c) → ArgTys → ArgTys

data WithArgs {c} : (ArgTys {c}) → Set (L.suc c) where
  [] : WithArgs []
  _∷_ : {A : Set c} → (a : A) → {AS : ArgTys} → WithArgs AS → WithArgs (A ArgTys.∷ AS)

record PartIso' {c a b} (TO : Set b) (argTys : ArgTys {c}) (args : WithArgs argTys) : Set (L.suc (a L.⊔ b L.⊔ c)) where
  field FROM : Set a -- agda type
  field there : Conversion FROM TO
  field back : Conversion TO FROM
  
record PartIso {c a b} (argTys : ArgTys {c}) : Set (L.suc (a L.⊔ b L.⊔ c)) where
  field TO : Set b -- haskell type
  field other : (args : WithArgs argTys) → PartIso' {c} {a} {b} TO argTys args

getFromType : ∀ {a b c argTys} → PartIso {c} {a} {b} argTys → WithArgs argTys → Set a
getFromType p args = PartIso'.FROM (PartIso.other p args)
