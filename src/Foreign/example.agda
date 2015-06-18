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
