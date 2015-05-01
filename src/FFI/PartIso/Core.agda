module FFI.PartIso.Core where

open import Level
open import Relation.Nullary
open import Data.Maybe

data Conversion {a b} (A : Set a) (B : Set b) : Set (suc (a ⊔ b)) where
  total : (A → B) → Conversion A B
  withDec : (A → Dec B) → Conversion A B
  withMaybe : (A → Maybe B) → Conversion A B
  fail : Conversion A B

record PartIso {a b} (A : Set a) (B : Set b) : Set (suc (a ⊔ b)) where
  field a2b : Conversion A B
  field b2a : Conversion B A

switchDirection : ∀ {a b} {A : Set a} {B : Set b} → (PartIso A B) → (PartIso B A)
switchDirection p = record { a2b = PartIso.b2a p ; b2a = PartIso.a2b p }
