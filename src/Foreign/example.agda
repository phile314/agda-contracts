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


  head : ∀ {a} → List a → a
    using foreign (record { foreign-spec = (HS-UHC "Data.List.head" (∀' (( ty (quote List) (Data.ForeignData.foreign-spec blub) ) ⇒ (var 0)) )) } )

module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Foreign.Fancy
  open import Data.Maybe
  open import Data.Product
  open import Data.List

  instance
    bla : Data.ForeignData (quote ℤ)
    bla = record { foreign-spec = Data.HS-UHC "Integer" (quote ℤ)}

  ℕ⇔ℤ : PartIsoInt
  ℕ⇔ℤ = toIntPartIso partIso (quoteTerm partIso) (quoteTerm bla)
    where f : ℤ → Maybe ℕ
          f -[1+ n ] = nothing
          f (+ n) = just n
          partIso : PartIso
          partIso = mkPartIso [] [] (record { HSₜ = ℤ ; other = ℕ , ((withMaybe f) , (total (+_))) })

-- the special type syntax for using isomorpisms.
--  fty : Set
--  fty = ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩

  -- the special type syntax converted to the AST representation
  fde : T 0
  fde = π ( iso ℕ⇔ℤ [] [] ) ⇒ (π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] []))

  -- the ffi declaration, which has the type ℤ → ℤ → ℤ
  ffi : unquote (getAgdaLowType fde)
    using foreign (record { foreign-spec = (HS-UHC "(+)" (unquote (getFFI fde)))})

  -- the wrapper, which has the type ℕ → ℕ → ℕ
  -- this is the thing we want in the end.
  fhi : unquote (getAgdaHighType fde)
  fhi = {!fde!} --ffi_lift fde ffi

