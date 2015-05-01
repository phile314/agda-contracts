module FFI.PartIso.DefaultIsos where

open import FFI.PartIso.Core
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Integer as Integer
open import Data.Nat as Nat

ℕ<=>ℤ : PartIso ℕ ℤ
ℕ<=>ℤ = record { a2b = total (Integer.+_) ; b2a = withMaybe ℤ=>ℕ }
  where ℤ=>ℕ : ℤ → Maybe ℕ
        ℤ=>ℕ -[1+ n ] = nothing
        ℤ=>ℕ (+ n) = just n

open import Data.List as List
open import Data.Vec as Vec

Vec<=>List : ∀ {n a} {A : Set a} → PartIso (Vec A n) (List A)
Vec<=>List {n} {_} {A} = record { a2b = total Vec.toList ; b2a = withMaybe List=>Vec }
  where List=>Vec : {n : ℕ} → List A → Maybe (Vec A n)
        List=>Vec {n} xs with List.length xs Nat.≟ n
        List=>Vec xs | yes refl = just (Vec.fromList xs)
        List=>Vec xs | no ¬p = nothing
