module Contracts.example where

module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Contracts.Base
  open import Data.Maybe
  open import Data.Product
  open import Data.List
  import Level

  ℕ⇔ℤ : PartIsoInt
  ℕ⇔ℤ = toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    where f : ℤ → Maybe ℕ
          f -[1+ n ] = nothing
          f (+ n) = just n
          partIso : PartIso
          partIso = mkPartIso [] [] (record { HSₜ = ℤ ; other = ℕ , ((withMaybe f) , (total (+_))) })

  

-- the special type syntax for using isomorpisms.
--  fty : Set
--  fty = ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩

  -- the internal AST representation of the above notation
  addType : T {Level.zero} 0
  addType = π ( iso ℕ⇔ℤ [] [] ) ⇒ (π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] []))
--  addType = π ( def_∙_ (quote ℤ) {quote bla} [] ) ⇒ (π (def_∙_ (quote ℤ) {quote bla} []) ⇒ (def_∙_ (quote ℤ) {quote bla} []))

  -- the ffi declaration, which has the type ℤ → ℤ → ℤ
  -- this is not terribly interesting....
--  add' : unquote (getAgdaLowType addType)
--    using foreign (record { foreign-spec = (HS-UHC "UHC.Agda.Builtins.primHsAdd" (unquote (getFFI addType)))})

  -- the wrapper, which has the type ℕ → ℕ → ℕ
  -- this is the thing we want in the end.
  -- The ffi-lift function does the heavy lifting,
  -- by producing a term which inserts the contracts checks where necessary.
--  add : unquote (getAgdaHighType addType)
--  add = unquote (ffi-lift addType (quote add'))


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

  list⇒vec : ∀ {l} {n : ℕ} {A : Set l} → List A → Maybe (Vec A n)
  list⇒vec {_} {n} xs with n N.≟ L.length xs
  list⇒vec xs | yes refl = just (Data.Vec.fromList xs)
  list⇒vec xs | no ¬p = nothing

  vec⇔list : {l : Level} → PartIsoInt {l}
  vec⇔list {l} = toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    where
    partIso : PartIso
    partIso = mkPartIso L.[ Set l ] L.[ (Lift ℕ) ]
      (λ a → record
        { HSₜ = L.List a
        ; other = λ n → (Vec a (lower n)) , ( withMaybe list⇒vec , Conversion.total Data.Vec.toList)})

module NatIntIso where
  open import Contracts.Base
  open import Data.Nat
  open import Data.Integer
  open import Data.Maybe
  open import Data.List
  open import Data.Product

  ℕ⇔ℤ : PartIsoInt
  ℕ⇔ℤ = toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    where f : ℤ → Maybe ℕ
          f -[1+ n ] = nothing
          f (+ n) = just n
          partIso : PartIso
          partIso = mkPartIso [] [] (record { HSₜ = ℤ ; other = ℕ , ((withMaybe f) , (Conversion.total (+_))) })


module MapEx where
  open VecIso
  open NatIntIso
  open import Contracts.Base
  open import Level
  open import Data.List
  open import Data.Integer
  open import Data.Nat

  mapImpl : (ℤ → ℤ) → List ℤ → List ℤ
  mapImpl f [] = []
  mapImpl f (x ∷ xs) = f x ∷ mapImpl f xs

  -- map higher order fun, where we convert the inputs of the higher order thingie
  mapNZType : T {Level.zero} 0
  mapNZType =
      π (
--        π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] [])
        π (def (quote ℤ) ∙ []) ⇒ (def (quote ℤ) ∙ [])
        )
    ⇒ (π (def (quote List) ∙ [ (def (quote ℤ) ∙ []) ])
    ⇒ (def (quote List) ∙ [ (def (quote ℤ) ∙ []) ]))

--  k : {!!}
--  k = {!unquote (ffi-lift mapNZType (quote mapImpl))!}

  myMap : unquote (getAgdaHighType mapNZType)
  myMap = unquote (ffi-lift mapNZType (quote mapImpl))

  k : {!unquote (getAgdaHighType mapNZType)!}
  k = {! unquote (ffi-lift mapNZType (quote mapImpl))!}
--  k' : {!unquote (getAgdaHighType mapNZType)!}
--  k' = {!myMap!}

module DepCon1 where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin

  mapImpl2 : (n : ℕ) (A : Set) (B : Set) → (A → B) → List A → List B
  mapImpl2 n A B = L.map

{-  mapNZType : T {Level.zero} 0
  mapNZType =
    π def quote ℕ ∙ [] -- n
    ⇒ (π set 0 -- A
    ⇒ (π set 0 -- B
    ⇒ (π (
      π var # 1 ∙ []
      ⇒ (var # 1 ∙ [])) -- f
    ⇒ (π iso vec⇔list [ var # 2 ∙ [] ] [ var # 3 ∙ [] ] -- vec
    ⇒ iso vec⇔list [ var # 2 ∙ [] ] [ var # 4 ∙ [] ] ))))

  lowType : Set (Level.suc Level.zero)
  lowType = unquote (getAgdaLowType mapNZType)

  lk : {!!}
  lk = {!unquote (getAgdaHighType mapNZType)!}

  myMap2 : unquote (getAgdaHighType mapNZType)
  myMap2 = {!unquote (ffi-lift mapNZType (quote mapImpl2))!}
  -}
    
module DepCon where
  open VecIso
  open import Data.Vec as Vec hiding ([_])
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List
  open import Data.Fin

  mapImpl2 : (n : ℕ) (A : Set) (B : Set) → (A → B) → Vec A n → Vec B n
  mapImpl2 n A B = Vec.map

--  lifth : ℕ → Lift ℕ
--  lifth = {!!}

  mapNZType : T {Level.zero} 0
  mapNZType =
    π def quote ℕ ∙ [] -- n
    ⇒ (π set 0 -- A
    ⇒ (π set 0 -- B
    ⇒ (π (
      π var # 1 ∙ []
      ⇒ (var # 1 ∙ [])) -- f
    ⇒ (π iso vec⇔list [ var # 2 ∙ [] ] [ var # 3 ∙ [] ] -- vec
    ⇒ iso vec⇔list [ var # 2 ∙ [] ] [ var # 4 ∙ [] ] ))))

  lowType : Set (Level.suc Level.zero)
  lowType = unquote (getAgdaLowType mapNZType)

  lk : {!!}
  lk = {!unquote (getAgdaHighType mapNZType)!}

  myMap2 : unquote (getAgdaHighType mapNZType)
  myMap2 = {!unquote (ffi-lift mapNZType (quote mapImpl2))!}
    

-- surface syntax tests
module T3 where
  open Ex2
  open VecIso
  open import Contracts.Base
  open import Data.Nat as N
  open import Level
  
{-  ⟨_∙_⟩ : ∀ {l} → PartIsoInt {l} → List ? → Set l
  ⟨ p ⟩ = {!!}
-}
  open import Data.List as L
  open import Data.Vec
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Data.Product

  getArgs : ∀ {l} → PartIsoInt {l} → Set (Level.suc l)
  getArgs p = WithArgs ((PartIso.ALLₐ h) L.++ ( PartIso.AGDAₐ h))
    where h = PartIsoInt.wrapped p

  data AST {l m} : Set (Level.suc (Level.suc (l Level.⊔ m )))

  getTy : ∀ {l} → AST {l} {l} → Set l --(l Level.⊔ m )

  data AST {l m} where
    pi : (a : AST {l} {l}) → (getTy a → AST {m} {m}) → AST
    ⟦_⟧ : (A : Set l) → AST -- normal type (List, Nat, etc..)
    ⟦_⇋_⟧ : (pi : PartIsoInt {l}) → getArgs pi → AST -- isomorphism

  split++ : ∀ {l} {a : ArgTys {l}} → {b : ArgTys {l}} → (args : WithArgs (a L.++ b)) → (WithArgs a × WithArgs b)
  split++ {a = []} args = [] , args
  split++ {a = x ∷ a} (a₁ , args) = (a₁ , (proj₁ r)) , (proj₂ r)
    where r = split++ args

  getTy (pi a x) = (arg : getTy a) → (getTy (x arg))
  getTy (⟦ x ⟧) = x
  getTy (⟦ x ⇋ x₁ ⟧) = proj₁ (applyArgs (PartIso'.other g) (proj₂ k)) --(PartIso.iso h) x₁
    where h = PartIsoInt.wrapped x
          k = split++ {_} {PartIso.ALLₐ h} x₁
          g = applyArgs (PartIso.iso h) (proj₁ k)

  id : ∀ {a} {A : Set a} → A → A
  id x = x

  syntax pi e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇒ e₂
  syntax id e = ⟨ e ⟩

  -- an example how the contracts syntax could look like,
  -- if implemented using normal Agda constructs.
  ty' : AST
  ty' = ⟨ a ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
    ⟨ y ∷ ⟦ vec⇔list ⇋ a , ((lift x) , []) ⟧ ⟩⇒
    ⟨ xs ∷ ⟦ List a ⟧ ⟩⇒
    ⟨ ⟦ List a ⟧ ⟩

  open import Reflection
--  f : Term
--  f = quoteTerm ( ⟨ n ∷ ℕ ⟩⇒ ( ⟨ x ∷ ℕ ⟩⇒ ⟨ (vec⇔list Level.zero ⇄ cons n nil) ⟩ ) )

--  g : {! definition (quote ty')!}
--  g = {!!}

  postulate mkForeign : {a : Set} → a

--  q : ℕ → ℕ
--  q = tactic t

--  q' : ℕ → ℕ
--  q' = quoteGoal g in unquote {!g!}

--  r : ℕ → ℕ
--    using foreign (record {})



open import IO
import IO.Primitive
open import Data.Unit
open import Data.Nat.Show
open import Data.List
open import Data.Integer
open import Data.Nat

open MapEx

postulate exError : {A : Set} → A

{-
main : IO.Primitive.IO ⊤
main = run (putStrLn (Data.Integer.show q))
  where p : List ℤ
        p = [ + 14 ]
        kk = myMap (Data.Nat._+_ 34) p
        q : ℤ
        q with kk
        q | [] = exError
        q | i ∷ _ = i
-}
