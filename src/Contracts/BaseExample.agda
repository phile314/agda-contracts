{-# OPTIONS --type-in-type #-}

module Contracts.BaseExample where

open import Contracts.Isos

tt' = quoteTerm tt
  where open import Data.Unit

module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Contracts.Base
  open import Data.Maybe
  open import Data.Product
  open import Data.List
  open import Data.Vec
  open NatIntIso
  import Level


-- the special type syntax for using isomorpisms.
--  fty : Set
--  fty = ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩

  -- the internal AST representation of the above notation
  addType : T 0
  addType = π ( iso ℕ⇔ℤ' tt' tt' tt' ) ∣ Keep ⇒ (π (iso ℕ⇔ℤ' tt' tt' tt') ∣ Keep ⇒ (iso ℕ⇔ℤ' tt' tt' tt'))
--  addType = π ( def_∙_ (quote ℤ) {quote bla} [] ) ⇒ (π (def_∙_ (quote ℤ) {quote bla} []) ⇒ (def_∙_ (quote ℤ) {quote bla} []))

  -- the ffi declaration, which has the type ℤ → ℤ → ℤ
  -- this is not terribly interesting....
--  add' : unquote (getAgdaLowType addType)
--    using foreign (record { foreign-spec = (HS-UHC "UHC.Agda.Builtins.primHsAdd" (unquote (getFFI addType)))})
  add' : ℤ → ℤ → ℤ
  add' = Data.Integer._+_

  -- the wrapper, which has the type ℕ → ℕ → ℕ
  -- this is the thing we want in the end.
  -- The ffi-lift function does the heavy lifting,
  -- by producing a term which inserts the contracts checks where necessary.
  add : unquote (deriveHighType addType)
  add = unquote (contract-apply addType (def (quote add') [])) -- unquote (ffi-lift addType (quote add'))
    where open import Reflection


module MapEx where
  open VecIso
  open NatIntIso
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Integer
  open import Data.Nat
  import Data.Vec as V
  open import Reflection

  mapImpl : (ℤ → ℤ) → L.List ℤ → L.List ℤ
  mapImpl f L.[] = L.[]
  mapImpl f (x L.∷ xs) = f x L.∷ mapImpl f xs

  -- map higher order fun, where we convert the inputs of the higher order thingie
  mapNZType : T 0
  mapNZType =
      π (
        π (iso ℕ⇔ℤ' tt' tt' tt') ∣ Keep ⇒ (iso ℕ⇔ℤ' tt' tt' tt')
--        π (def (quote ℤ) ∙ []) ⇒ (def (quote ℤ) ∙ [])
        ) ∣ Keep
    ⇒ (π (agda-ty (quoteTerm (L.List ℤ))) ∣ Keep
    ⇒ (agda-ty (quoteTerm (L.List ℤ))))

  myMap : unquote (deriveHighType mapNZType) --unquote (getAgdaHighType mapNZType)
  myMap = unquote (contract-apply mapNZType (quoteTerm mapImpl))


module DepSimple where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin
  import Data.Vec as V
  open import Reflection

  mapImpl2 : (n : ℕ) (A : Set) → List A
  mapImpl2 n A = []

  mapNZType : T 0
  mapNZType =
    π (agda-ty (def (quote ℕ) [])) ∣ Keep -- n
    ⇒ (π (agda-ty (quoteTerm Set)) ∣ Keep -- A
    ⇒ (iso (vec⇔list') (var 0 []) tt' (var 1 []) ))

  import Agda.Primitive
  import Data.Product

  fixType : (A : Set) → A → A
  fixType _ x = x

  import Data.Nat.Base
  import Data.List.Base
  import Data.Vec

  myMap2 : unquote (deriveHighType mapNZType)
  myMap2 = unquote (contract-apply mapNZType (def (quote mapImpl2) []))


{-
module DepCon1 where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin
  import Data.Vec as V
  open import Reflection

  mapImpl2 : (A : Set) → (B : Set) → (A → B) → List A → List B
  mapImpl2 A B = L.map

  mapNZType : T 0
  mapNZType =
    π ( def quote ℕ ∙ []) ∣ Discard -- n
    ⇒ ( π set 0 ∣ Keep -- A
    ⇒ ( π set 0 ∣ Keep -- B
    ⇒ ( π (
      π (var # 1 ∙ []) ∣ Keep
      ⇒ (var # 1 ∙ [])) ∣ Keep -- f
      
    ⇒ (π iso (vec⇔list') ( var 2 []) tt' (var 3 []) ∣ Keep -- vec
--    ⇒ (π (def (quote List) ∙ L.[ var # 1 ∙ [] ]) ∣ Keep
--    ⇒ (def (quote List) ∙ L.[ var # 3 ∙ [] ] )  ))))  --)
    ⇒ iso (vec⇔list') (var 2 []) tt' (var 4 [])))))


  import Agda.Primitive
  import Data.Product

  fixType : (A : Set) → A → A
  fixType _ x = x

  import Data.Nat.Base


  myMap2 : unquote (getAgdaHighType mapNZType)
--  myMap2 : {!unquote (getAgdaHighType mapNZType)!} --unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
--  myMap2 =  {!pretty (elimLets (ffi-lift mapNZType (quote mapImpl2)))!}
--  myMap2 = {!pretty (ffi-lift mapNZType (def (quote mapImpl2) []))!}
  myMap2 = unquote (ffi-lift mapNZType (def (quote mapImpl2) [])) -- unquote (ffi-lift mapNZType (quote mapImpl2))
    where open import Reflection
  
    
module DepCon where
  open VecIso
  open import Data.Vec as Vec hiding ([_])
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List
  open import Data.Fin
  open import Reflection

  mapImpl2 : (n : ℕ) (A : Set) (B : Set) → (A → B) → Vec A n → Vec B n
  mapImpl2 n A B = Vec.map

{-
  mapNZType : T {Level.zero} 0
  mapNZType =
    π def quote ℕ ∙ [] -- n
    ⇒ (π set 0 -- A
    ⇒ (π set 0 -- B
    ⇒ (π (
      π var # 1 ∙ []
      ⇒ (var # 1 ∙ [])) -- f
    ⇒ (π iso vec⇔list [ var # 2 ∙ [] ] [ var # 3 ∙ [] ] -- vec A n
    ⇒ iso vec⇔list [ var # 2 ∙ [] ] [ var # 4 ∙ [] ] )))) -- ) vec B n

  lowType : Set (Level.suc Level.zero)
  lowType = unquote (getAgdaLowType mapNZType)

  lk : {!pretty (quoteTerm (ℕ → (A B : Set) → (f : A -> B) -> List A -> List B))!}
  lk = {!unquote (getAgdaHighType mapNZType)!}
  open import Data.Product
  open import Function

  k : ℕ → Set → Conversions {!!} {!!}
  k n A = {!!}
    where 

  myMap2 : unquote (getAgdaHighType mapNZType)
--  myMap2 = unquote (ffi-lift mapNZType (quote mapImpl2))
  myMap2 = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}
    
-}


open import IO
import IO.Primitive
open import Data.Unit
open import Data.Nat.Show
import Data.List
open import Data.Integer
open import Data.Nat

--open MapEx
open DepCon1
open import Data.Vec

postulate exError : {A : Set} → A

{-
main : IO.Primitive.IO ⊤
main = run (putStrLn (Data.Nat.Show.show s))
  where n = 3
        p : Vec ℤ n
        p = + 0 ∷ (-[1+ 48 ] ∷ (+ 13 ∷ []))
        kk = myMap2 n ℤ ℕ (∣_∣) p

        s = foldl (λ _ → ℕ) Data.Nat._+_ 0 kk

-}
-}
