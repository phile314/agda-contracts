module Contracts.example where

open import Foreign.Base

open Foreign.Base.Fun

module Ex1 where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  {-# COMPILED_DATA_UHC List __LIST__ __NIL__ __CONS__ #-}

  blub : Data.ForeignData (quote List)
  blub = record { foreign-spec = Data.HS-UHC "Data.List.List" (quote List) }


--  head : ∀ {a} → List a → a
--    using foreign (record { foreign-spec = (HS-UHC "Prelude.head" (∀' (( ty (quote List) (Data.ForeignData.foreign-spec blub) ) ⇒ (var 0)) )) } )

module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Contracts.Base
  open import Data.Maybe
  open import Data.Product
  open import Data.List
  open Foreign.Base.HS
  import Level

{-  instance
    bla : Data.ForeignData (quote ℤ)
    bla = record { foreign-spec = Data.HS-UHC "Integer" (quote ℤ)}-}

  postulate
    ℤ⇒HSInteger : ℤ → HSInteger
    HSInteger⇒ℤ : HSInteger → ℤ
  {-# COMPILED_UHC ℤ⇒HSInteger UHC.Agda.Builtins.primAgdaIntegerToHsInteger #-}
  {-# COMPILED_UHC HSInteger⇒ℤ UHC.Agda.Builtins.primHsIntegerToAgdaInteger #-}

  ℕ⇔Hsℤ : PartIsoInt
  ℕ⇔Hsℤ = toIntPartIso partIso (quote partIso) (quoteTerm partIso) (quoteTerm HSInteger-FD)
    where f : HSInteger → Maybe ℕ
          f i with HSInteger⇒ℤ i
          ... | -[1+ n ] = nothing
          ... | (+ n) = just n
          g : ℕ → HSInteger
          g n = ℤ⇒HSInteger (+ n)
          partIso : PartIso
          partIso = mkPartIso [] [] (record { HSₜ = HSInteger ; other = ℕ , ((withMaybe f) , (total (g))) })

  

-- the special type syntax for using isomorpisms.
--  fty : Set
--  fty = ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩

  -- the internal AST representation of the above notation
  addType : T {Level.zero} 0
  addType = π ( iso ℕ⇔Hsℤ [] [] ) ⇒ (π (iso ℕ⇔Hsℤ [] []) ⇒ (iso ℕ⇔Hsℤ [] []))
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

  instance
    HSList-FD : Data.ForeignData (quote List)
    HSList-FD = record { foreign-spec = Data.HS-UHC "Data.List.List" (quote List) }
  
  list⇒vec : ∀ {l} {n : ℕ} {A : Set l} → List A → Maybe (Vec A n)
  list⇒vec {_} {n} xs with n N.≟ L.length xs
  list⇒vec xs | yes refl = just (Data.Vec.fromList xs)
  list⇒vec xs | no ¬p = nothing

  vec⇔list : (l : Level) → PartIsoInt {l}
  vec⇔list l = toIntPartIso partIso (quote partIso) (quoteTerm partIso) {{HSList-FD}} (quoteTerm HSList-FD)
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

  -- NOT WOKRING - JUST TO GET STUFF TO TYPE CHECK!!!
  instance
    ℤ-FD : Data.ForeignData (quote ℤ)
    ℤ-FD = record { foreign-spec = Data.HS-UHC "DUMMY NOT WORKING" (quote ℤ) }

  ℕ⇔ℤ : PartIsoInt
  ℕ⇔ℤ = toIntPartIso partIso (quote partIso) (quoteTerm partIso) (quoteTerm ℤ-FD)
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
        π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] [])
--        π (iso ℕ⇔ℤ [] []) ⇒ (def (quote ℤ) ∙ [])
        )
    ⇒ (π (def (quote List) ∙ [ (def (quote ℤ) ∙ []) ])
    ⇒ (def (quote List) ∙ [ (def (quote ℤ) ∙ []) ]))

--  k : {!!}
--  k = {!unquote (ffi-lift mapNZType (quote mapImpl))!}

  myMap : unquote (getAgdaHighType mapNZType)
  myMap = unquote (ffi-lift mapNZType (quote mapImpl))

--  k' : {!unquote (getAgdaHighType mapNZType)!}
--  k' = {!myMap!}

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
    ⟨ x ∷ ⟦ ℕ⇔Hsℤ ⇋ [] ⟧ ⟩⇒
    ⟨ y ∷ ⟦ vec⇔list Level.zero ⇋ a , ((lift x) , []) ⟧ ⟩⇒
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

main : IO.Primitive.IO ⊤
main = run (putStrLn (Data.Integer.show q))
  where p : List ℤ
        p = [ + 14 ]
        k = myMap (Data.Nat._+_ 34) p
        q : ℤ
        q with k
        q | [] = exError
        q | i ∷ _ = i
