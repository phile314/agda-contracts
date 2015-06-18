module Foreign.example where

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
  open import Foreign.Fancy
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

  ℕ⇔ℤ : PartIsoInt
  ℕ⇔ℤ = toIntPartIso partIso (quote partIso) (quoteTerm partIso) (quoteTerm HSInteger-FD)
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

  -- the special type syntax converted to the AST representation
  fde : T {Level.zero} 0
  fde = π ( iso ℕ⇔ℤ [] [] ) ⇒ (π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] []))
--  fde = π ( def_∙_ (quote ℤ) {quote bla} [] ) ⇒ (π (def_∙_ (quote ℤ) {quote bla} []) ⇒ (def_∙_ (quote ℤ) {quote bla} []))

  -- the ffi declaration, which has the type ℤ → ℤ → ℤ
  ffi : unquote (getAgdaLowType fde)
    using foreign (record { foreign-spec = (HS-UHC "UHC.Agda.Builtins.primHsAdd" (unquote (getFFI fde)))})

  -- the wrapper, which has the type ℕ → ℕ → ℕ
  -- this is the thing we want in the end.
  fhi : unquote (getAgdaHighType fde)
  fhi = unquote (ffi-lift fde (quote ffi)) -- {!ffi-lift fde (quote ffi)!} --ffi_lift fde ffi

--  t : {!!}
--  t = {!unquote (ffi-lift fde (quote ffi))!}

open import IO
import IO.Primitive
open import Data.Unit
open import Data.Nat.Show

open Ex2

main : IO.Primitive.IO ⊤
main = run (putStrLn (show k))
  where k = fhi 12 45


module T3 where
  open import Foreign.Fancy
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
        
--  { HSₐ = List.[ Set ]
--  ; AGDAₐ = List.[ Lift ℕ ]
--  ; iso = λ x → L.lift ((List (Lift x)) , (λ x₁ → L.lift (record { AGDA = Vec (Lift x) (lower x₁) })))
--  }
 
{-  f : {n : ⟨ ℕ⇔ℤ ⟩} → {!!} → {!!}
  f = {!!}-}
{-  postulate
    pi : (A : Set) → (A → Set) → Set
    val : ∀ {a} {A : Set a} → A → Set-}

{-  data HList : Set₁ where
    nil : HList
    cons : {A : Set} → A → HList → HList

  data AST {l m} : Set (Level.suc (Level.suc (l Level.⊔ m))) where
    pi : (A : Set l) → (A → AST {l} {m} ) → AST
    val : {A : Set m} → A → AST
    iso : PartIsoInt {m} → HList → AST
    

  syntax pi e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇒ e₂
  syntax val e = ⟨ e ⟩
  syntax iso p xs = p ⇄ xs

-}

  data HList {l} : Set (Level.suc l) where
    nil : HList
    cons : Set l → HList → HList

  getArgs : ∀ {l} → PartIsoInt {l} → Set (Level.suc l)
  getArgs p = WithArgs ((PartIso.ALLₐ h) L.++ ( PartIso.AGDAₐ h))
    where h = PartIsoInt.wrapped p

  data AST {l m} : Set (Level.suc (Level.suc (l Level.⊔ m )))

  getTy : ∀ {l} → AST {l} {l} → Set l --(l Level.⊔ m )

  data AST {l m} where
    pi : (a : AST {l} {l}) → (getTy a → AST {m} {m}) → AST
    ⟦_⟧ : (A : Set l) → AST
    ⟦_⇋_⟧ : (pi : PartIsoInt {l}) → getArgs pi → AST

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
--  syntax val e = ⟨ e ⟩
--  syntax iso p xs = p ⇄ xs

  ty' : AST
  ty' = ⟨ a ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
    ⟨ y ∷ ⟦ vec⇔list Level.zero ⇋ a , ((lift x) , []) ⟧ ⟩⇒
    ⟨ xs ∷ ⟦ List a ⟧ ⟩⇒
    ⟨ ⟦ List a ⟧ ⟩

  open import Reflection
--  f : Term
--  f = quoteTerm ( ⟨ n ∷ ℕ ⟩⇒ ( ⟨ x ∷ ℕ ⟩⇒ ⟨ (vec⇔list Level.zero ⇄ cons n nil) ⟩ ) )

  g : {! definition (quote f)!}
  g = {!!}
