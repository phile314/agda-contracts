module Contracts.example where

module NatIntIso where
  open import Contracts.Base
  open import Data.Nat
  open import Data.Integer
  open import Data.Maybe
  open import Data.List
  open import Data.Product

  ℕ⇔ℤ : PartIsoInt
  ℕ⇔ℤ = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrappedₙ = quote partIso ; wrapped = partIso}
    where f : ℤ → Maybe ℕ
          f -[1+ n ] = nothing
          f (+ n) = just n
          partIso : PartIso
          partIso = mkPartIso [] [] (ℤ , (ℕ , ((withMaybe f) , (total (ℤ.+_)))))


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
  addType : T {Level.zero} 0
  addType = π ( iso ℕ⇔ℤ [] [] ) ⇒ (π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] []))
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
  add = unquote (ffi-lift addType (quote add'))


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
  vec⇔list {l} = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrappedₙ = quote partIso ; wrapped = partIso }
    where
    partIso : PartIso
    partIso = mkPartIso L.[ Lift {_} {l} (Set l) ] L.[ (Lift ℕ) ]
      (λ x → (List (lower x)) , (λ x₁ → (Vec (lower x) (lower x₁)) , ((withMaybe list⇒vec) , (total Data.Vec.toList))))


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
  mapNZType : T {Level.zero} 0
  mapNZType =
      π (
        π (iso ℕ⇔ℤ V.[] V.[]) ⇒ (iso ℕ⇔ℤ V.[] V.[])
--        π (def (quote ℤ) ∙ []) ⇒ (def (quote ℤ) ∙ [])
        )
    ⇒ (π (def (quote L.List) ∙ [ (def (quote ℤ) ∙ []) ])
    ⇒ (def (quote L.List) ∙ [ (def (quote ℤ) ∙ []) ]))

  myMap : unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
  myMap = unquote (ffi-lift mapNZType (quote mapImpl))

module DepCon1 where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin
  import Data.Vec as V
  open import Reflection

  mapImpl2 : (n : ℕ) (A : Set) (B : Set) → (A → B) → List A → List B
  mapImpl2 n A B = L.map

  mapNZType : T {Level.zero} 0
  mapNZType =
    π def quote ℕ ∙ [] -- n
    ⇒ (π set 0 -- A
    ⇒ (π set 0 -- B
    ⇒ (π (
      π var # 1 ∙ []
      ⇒ (var # 1 ∙ [])) -- f
    ⇒ (π iso vec⇔list V.[ var # 2 ∙ [] ] V.[ var # 3 ∙ [] ] -- vec
    ⇒ iso vec⇔list V.[ var # 2 ∙ [] ] V.[ var # 4 ∙ [] ] ))))

--  lowType : Set (Level.suc Level.zero)
--  lowType = {!!} --unquote (getAgdaLowType mapNZType)

--  lk : {!!}
--  lk = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}

  import Agda.Primitive
  import Data.Product

  partIso : PartIso {Level.zero}
  partIso = PartIsoInt.wrapped VecIso.vec⇔list

  fixType : ∀ {a} (A : Set a) → A → A
  fixType _ x = x


  myMap2 : unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
--  myMap2 =  {!pretty (elimLets (ffi-lift mapNZType (quote mapImpl2)))!}
  myMap2 = unquote (ffi-lift mapNZType (quote mapImpl2)) -- unquote (ffi-lift mapNZType (quote mapImpl2))
  
    
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
  getArgs p = WithArgs ((PartIso.LOWₐ h) L.++ ( PartIso.HIGHₐ h))
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
  getTy (⟦ x ⇋ x₁ ⟧) = proj₁ (applyArgs (proj₂ g) (proj₂ k)) --(PartIso.iso h) x₁
    where h = PartIsoInt.wrapped x
          k = split++ {_} {PartIso.LOWₐ h} x₁
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
    ⟨ y ∷ ⟦ vec⇔list ⇋ lift a , ((lift x) , []) ⟧ ⟩⇒
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
import Data.List
open import Data.Integer
open import Data.Nat

--open MapEx
open DepCon1
open import Data.Vec

postulate exError : {A : Set} → A


main : IO.Primitive.IO ⊤
main = run (putStrLn (Data.Nat.Show.show s))
  where n = 3
        p : Vec ℤ n
        p = + 0 ∷ (-[1+ 48 ] ∷ (+ 13 ∷ []))
        kk = myMap2 n ℤ ℕ (∣_∣) p

        s = foldl (λ _ → ℕ) Data.Nat._+_ 0 kk

