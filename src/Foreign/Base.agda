module Foreign.Base where

open import Level
open import Data.String
open import Reflection using (Name; showName)

data FFIWay : Set where
  HS-UHC : FFIWay
{--# FFIWAY FFIWay #--}
{--# FFIWAYHSUHC HS_UHC #--}

HS-UHC-EntityName : Set
HS-UHC-EntityName = String

module Data where

  -- the mapping is not stored inside the ForeignSpec,
  -- the ForeignData is just used to servce as proof object.
  data ForeignSpec : FFIWay → Set where
    HS-UHC : HS-UHC-EntityName -- name is only used for debugging
      → ForeignSpec HS-UHC

  record ForeignData (way : FFIWay) (nm : Name) : Set where
    field foreign-spec : ForeignSpec way

module Fun where

  open import Data.Nat
  open import Data.Fin
  -- The grammar of Haskell types, using de-bruijn indices.
  data τ-Hs {way : FFIWay} : ℕ → Set where
    var : ∀ {n} (k : Fin n) → τ-Hs n
    app : ∀ {n} → (τ-Hs {way = way} n) → (τ-Hs {way = way} n) → τ-Hs n
    ∀'  : ∀ {n} → (τ-Hs {way = way} (ℕ.suc n)) → τ-Hs n
    _⇒_ : ∀ {n} → (τ-Hs {way = way} n) → (τ-Hs {way = way} n) → τ-Hs n
    ty  : ∀ {n} → (nm-Agda : Name) → {{foreign : Data.ForeignData way nm-Agda}} → τ-Hs n

  data ForeignSpec : FFIWay → Set where
    HS-UHC : HS-UHC-EntityName → τ-Hs {HS-UHC} 0 → ForeignSpec HS-UHC

  record ForeignFun (way : FFIWay) : Set where
    field foreign-spec : ForeignSpec way

  open import Data.List using (List; foldl)
  apps : ∀ {n way} → (τ-Hs {way = way} n) → List (τ-Hs {way = way} n) → τ-Hs {way = way} n
  apps f xs = foldl app f xs

  import Data.Vec as V
  open import Data.Maybe
  import Data.Nat.Show as NS
  Γ : ℕ → Set
  Γ n = V.Vec String n
  show-τ-Hs : ∀ {n way} → Γ n → (τ-Hs {way} n) → String
  show-τ-Hs c (var x) = V.lookup x c
  show-τ-Hs c (app t t₁) = "(" ++ show-τ-Hs c t ++ " " ++ show-τ-Hs c t₁ ++ ")"
  show-τ-Hs {n} c (∀' t) = "(∀ " ++ nm ++ " . " ++ show-τ-Hs (nm V.∷ c) t ++ ")"
    where nm = "a" ++ NS.show n
  show-τ-Hs c (t ⇒ t₁) = "(" ++ show-τ-Hs c t ++ " → " ++ show-τ-Hs c t₁ ++ ")"
  show-τ-Hs c (ty nm-Agda {{x}}) with Data.ForeignData.foreign-spec x
  show-τ-Hs c (ty nm-Agda {{x}}) | Data.HS-UHC x₁ = "⟨" ++ showName nm-Agda ++ " as " ++ x₁ ++ "⟩"

  showSpec : {way : FFIWay} → ForeignSpec way → Maybe String
  showSpec (HS-UHC x x₁) = just (x ++ " :: " ++ show-τ-Hs V.[] x₁)
