{-# OPTIONS --type-in-type #-}

module Contracts.example where

module NatIntIso where
  open import Contracts.Base
  open import Data.Nat
  open import Data.Integer
  open import Data.Maybe
  open import Data.List
  open import Data.Product
  open import Reflection
  
  ℕ⇔ℤI : PartIso
  ℕ⇔ℤI = mkPartIso [] [] (ℤ , (ℕ , ((withMaybe f) , (total (ℤ.+_)))))
    where f : ℤ → Maybe ℕ
          f -[1+ n ] = nothing
          f (+ n) = just n

  ℕ⇔ℤ' : PartIsoInt
  ℕ⇔ℤ' = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrappedₙ = def (quote ℕ⇔ℤI) [] } --; wrapped = partIso}


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
  addType = π ( iso ℕ⇔ℤ' [] [] ) ∣ Keep ⇒ (π (iso ℕ⇔ℤ' [] []) ∣ Keep ⇒ (iso ℕ⇔ℤ' [] []))
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
  add : unquote (getAgdaHighType addType)
  add = unquote (ffi-lift addType (def (quote add') [])) -- unquote (ffi-lift addType (quote add'))
    where open import Reflection


module VecIso where
  open import Data.List as L
  open import Data.Nat as N
  open import Data.Maybe
  open import Data.Vec
  open import Relation.Nullary
  open import Level
  open import Contracts.Base
  open import Relation.Binary.PropositionalEquality
  open import Data.Product

  list⇒vec : ∀ {n : ℕ} {A : Set} → List A → Maybe (Vec A n)
  list⇒vec {n} xs with n N.≟ L.length xs
  list⇒vec xs | yes refl = just (Data.Vec.fromList xs)
  list⇒vec xs | no ¬p = nothing

  vec⇔listI : PartIso
  vec⇔listI = mkPartIso L.[ Set ] L.[ ℕ ]
      (λ x → (List x) , (λ x₁ → (Vec x x₁) , ((withMaybe list⇒vec) , (total Data.Vec.toList))))


  vec⇔list' : PartIsoInt
  vec⇔list' = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrappedₙ = def (quote vl) [] } --; wrapped = partIso }
    where vl = vec⇔listI
          open import Reflection


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
        π (iso ℕ⇔ℤ' L.[] L.[]) ∣ Keep ⇒ (iso ℕ⇔ℤ' L.[] L.[])
--        π (def (quote ℤ) ∙ []) ⇒ (def (quote ℤ) ∙ [])
        ) ∣ Keep
    ⇒ (π (def (quote L.List) ∙ [ (def (quote ℤ) ∙ []) ]) ∣ Keep
    ⇒ (def (quote L.List) ∙ [ (def (quote ℤ) ∙ []) ]))

  myMap : unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
  myMap = unquote (ffi-lift mapNZType (quoteTerm mapImpl))

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
    π def quote ℕ ∙ [] ∣ Keep -- n
    ⇒ (π set 0 ∣ Keep -- A
    ⇒ iso (vec⇔list') L.[ var # 0 ∙ [] ] L.[ var # 1 ∙ [] ] )

--  lowType : Set (Level.suc Level.zero)
--  lowType = {!!} --unquote (getAgdaLowType mapNZType)

--  lk : {!!}
--  lk = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}

  import Agda.Primitive
  import Data.Product

--  partIso : PartIso {Level.zero}
--  partIso = PartIsoInt.wrapped VecIso.vec⇔list

  fixType : (A : Set) → A → A
  fixType _ x = x

  import Data.Nat.Base
  import Data.List.Base
  import Data.Vec

  myMap2 : unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
--  myMap2 =  {!pretty (elimLets (ffi-lift mapNZType (quote mapImpl2)))!}
  myMap2 = unquote (ffi-lift mapNZType (def (quote mapImpl2) [])) -- unquote (ffi-lift mapNZType (quote mapImpl2))

module DepCon1 where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin
  import Data.Vec as V
  open import Reflection

  mapImpl2 : {- ℕ →-} (A : Set) {-(B : Set)-} → (A → A) → List A → List A
  mapImpl2 A f xs = xs --L.map

  mapNZType : T 0
  mapNZType =
    π ( {-def quote ℕ ∙ []-} set 0) ∣ Keep -- n
    ⇒ ( π set 0 ∣ Keep -- A
--    ⇒ (π set 0 ∣ Keep -- B
    ⇒ (π (
      π var # 0 ∙ [] ∣ Keep
      ⇒ (var # 1 ∙ [])) ∣ Keep -- f
--    ⇒ (π iso (vec⇔list') L.[ var # 2 ∙ [] ] L.[ var # 3 ∙ [] ] ∣ Keep -- vec
    ⇒ (π (def (quote List) ∙ L.[ var # 1 ∙ [] ]) ∣ Keep
    ⇒ (def (quote List) ∙ L.[ var # 2 ∙ [] ] ))))
--    ⇒ iso (vec⇔list') L.[ var # 2 ∙ [] ] L.[ var # 4 ∙ [] ] ))))

--  lowType : Set (Level.suc Level.zero)
--  lowType = {!!} --unquote (getAgdaLowType mapNZType)

--  lk : {!!}
--  lk = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}

  import Agda.Primitive
  import Data.Product

--  partIso : PartIso {Level.zero}
--  partIso = PartIsoInt.wrapped VecIso.vec⇔list

  fixType : (A : Set) → A → A
  fixType _ x = x

  import Data.Nat.Base


  myMap2 : unquote (getAgdaHighType mapNZType)
--  myMap2 : {!unquote (getAgdaHighType mapNZType)!} --unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
--  myMap2 =  {!pretty (elimLets (ffi-lift mapNZType (quote mapImpl2)))!}
  myMap2 = {!pretty (ffi-lift mapNZType (def (quote mapImpl2) []))!}
--  myMap2 = unquote (ffi-lift mapNZType (def (quote mapImpl2) [])) -- unquote (ffi-lift mapNZType (quote mapImpl2))
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

--  lifth : ℕ → Lift ℕ
--  lifth = {!!}
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

{-  myMap2' : unquote (getAgdaHighType mapNZType)
  myMap2' = λ n → λ A → λ f → let f' : (x : A) → A
                                  f' = λ x → f x
                               in λ xs → let xs' = unsafeConvert {!!} xs
                                            in {!!}-}

  myMap2 : unquote (getAgdaHighType mapNZType)
--  myMap2 = unquote (ffi-lift mapNZType (quote mapImpl2))
  myMap2 = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}
    
-}
-- surface syntax tests
module T3 where
  open NatIntIso
  open VecIso
  open import Contracts.Base
  open import Data.Nat as N
  open import Level
  open import Contracts.SSyn
  
  open import Data.List as List
  open import Data.Vec
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Data.Product


  ℕ⇔ℤ : PartIsoPub
  ℕ⇔ℤ = record { partIso = ℕ⇔ℤI ; partIsoInt = ℕ⇔ℤ' }

  vec⇔list : PartIsoPub
  vec⇔list = record { partIso = vec⇔listI ; partIsoInt = (vec⇔list') }

  
  -- an example how the contracts syntax could look like,
  -- if implemented using normal Agda constructs.
{-  ty' : AST
  ty' = ⟨ a ∷ ⟦ Set₁ ⟧ ⟩⇒
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
    ⟨ y ∷ ⟦ vec⇔list ⇋ lift a , ((lift x) , []) ⟧ ⟩⇒
    ⟨ xs ∷ ⟦ List a ⟧ ⟩⇒
    ⟨ ⟦ List a ⟧ ⟩-}


  open import Function
  open import Reflection as R
  
  f' : AST
  f' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ liftW x , liftW n , [] ⟧ ⟩
  f : Term
  f = quoteTerm (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ liftW x , liftW n , [] ⟧ ⟩)

  f-low : ℕ → (A : Set) → List A
  f-low n A = []
  
--  g : {!  f!}
--  g = {!getAgdaHighType (ast⇒T' f)!}
  g' : AST
  g' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇏
    ⟨ x ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ f ∷ ⟦ (x → x) ⟧ ⟩⇒
    ⟨ ⟦ {!!} ⇋ {!!} ⟧ ⟩

--  gg : unquote (getAgdaHighType (ast⇒T' f))
--  gg = unquote (ffi-lift (ast⇒T' f) (def (quote f-low) []))

  ggg : {!!}
  ggg = {!gg!}

--  pp' : _
--  pp' = assert (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ x , n , [] ⟧ ⟩) f-low

  {-
  open import Data.Integer
  addImpl' : ℤ → ℤ → ℤ
  addImpl' a b = a Data.Integer.+ b

  addContr : Term
  addContr = quoteTerm (
        ⟨ a ∷ ⟦ ℤ ⟧ ⟩⇒ --⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
        ⟨ b ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
        ⟨ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩ )
--        ⟨ ⟦ vec⇔list ⇋ lift ℕ , lift n , [] ⟧ ⟩ )

--  add : unquote (getAgdaHighType (ast⇒T' addContr))
--  add = unquote (ffi-lift (ast⇒T' addContr) (quote addImpl'))


  
  open import Data.Bool
  lk : Bool → Term
  lk true = let x = {!open import Data.List!} in {!!}
  lk false = {!add ( -[1+ 30 ] ) (24)!}
    where open import Data.List public

  postulate mkForeign : {a : Set} → a
-}
--  q : ℕ → ℕ
--  q = tactic t

--  q' : ℕ → ℕ
--  q' = quoteGoal g in unquote {!g!}

--  r : ℕ → ℕ
--    using foreign (record {})

module Witnessss where
  open import Contracts.Witness
  open import Contracts.SSyn
  open import Data.Nat
  open import Data.List

  postulate f-low : ℕ → ℕ → ℕ

--  f' : _
--  f' = assert (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ (⇔Witness (_≟_ 10)) ⇋ {!!} ⟧ ⟩) f-low

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
