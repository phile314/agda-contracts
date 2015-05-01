module FFI.PartIso.DefaultIsos where

open import FFI.PartIso.Core
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Integer as Integer
open import Data.Nat as Nat
open import Level as L

ℕ<=>ℤ : PartIso {L.zero} []
ℕ<=>ℤ = record
  { TO = ℤ
  ; other = λ [] → record
    { FROM = ℕ
    ; there = total (Integer.+_)
    ; back = withMaybe ℤ=>ℕ
    }
  }
  where ℤ=>ℕ : ℤ → Maybe ℕ
        ℤ=>ℕ -[1+ n ] = nothing
        ℤ=>ℕ (+ n) = just n

open import Data.List as List
open import Data.Vec as Vec

Vec<=>List : ∀ {a} (A : Set a) → PartIso (ℕ ArgTys.∷ [])
Vec<=>List {a} A = record
  { TO = List A
  ; other = helper
  }
  where
    List=>Vec : {n : ℕ} → List A → Maybe (Vec A n)
    List=>Vec {n} xs with List.length xs Nat.≟ n
    List=>Vec xs | yes refl = just (Vec.fromList xs)
    List=>Vec xs | no ¬p = nothing

    argTys = (ℕ ArgTys.∷ [])
    helper : (args : WithArgs argTys) → PartIso' (List A) argTys args
    helper (n WithArgs.∷ x) = record
      { FROM = Vec A n
      ; there = total toList
      ; back = withMaybe List=>Vec
      }

-- test function...
f : (n : getFromType ℕ<=>ℤ []) → getFromType (Vec<=>List ℤ) (n WithArgs.∷ [])
f = {!!}
