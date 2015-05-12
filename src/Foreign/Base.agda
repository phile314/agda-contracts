module Foreign.Base where

open import Level
open import Data.String

data FFIWay : Set where
  HS_UHC : FFIWay
{--# FFIWAY FFIWay #--}
{--# FFIWAYHSUHC HS_UHC #--}

HS_UHC_EntityName : Set
HS_UHC_EntityName = String

module Data where

  -- the mapping is not stored inside the ForeignSpec,
  -- the ForeignData is just used to servce as proof object.
  data ForeignSpec : FFIWay → Set where
    HS_UHC : HS_UHC_EntityName -- name is only used for debugging
      → ForeignSpec HS_UHC

  record ForeignData {l} (way : FFIWay) (τ-Agda : Set l) : Set (suc l) where
    field foreign-spec : ForeignSpec way

module Fun where

  open import Data.Nat
  open import Data.Fin
  -- The grammar of Haskell types, using de-bruijn indices.
  data τ-Hs {l} {way : FFIWay} : ℕ → Set (Level.suc l) where
    var : ∀ {n} (k : Fin n) → τ-Hs n
    app : ∀ {n} → (τ-Hs {way = way} n) → (τ-Hs {way = way} n) → τ-Hs n
    ∀'  : ∀ {n} → (τ-Hs {way = way} (ℕ.suc n)) → τ-Hs n
    _⇒_ : ∀ {n} → (τ-Hs {way = way} n) → (τ-Hs {way = way} n) → τ-Hs n
    ty  : ∀ {n} → (τ-Agda : Set l) → Data.ForeignData way τ-Agda → τ-Hs n

  data ForeignSpec {l} : FFIWay → Set (Level.suc l) where
    HS_UHC : HS_UHC_EntityName → τ-Hs {l} {HS_UHC} 0 → ForeignSpec HS_UHC

  record ForeignFun {l} (way : FFIWay) : Set (Level.suc l) where
    field foreign-spec : ForeignSpec {l} way

  import Data.Vec as V
  open import Data.Maybe
  import Data.Nat.Show as NS
  Γ : ℕ → Set
  Γ n = V.Vec String n
  show-τ-Hs : ∀ {n l way} → Γ n → (τ-Hs {l} {way} n) → String
  show-τ-Hs c (var x) = V.lookup x c
  show-τ-Hs c (app t t₁) = "(" ++ show-τ-Hs c t ++ " " ++ show-τ-Hs c t₁ ++ ")"
  show-τ-Hs {n} c (∀' t) = "(∀ " ++ nm ++ " . " ++ show-τ-Hs (nm V.∷ c) t ++ ")"
    where nm = "a" ++ NS.show n
  show-τ-Hs c (t ⇒ t₁) = "(" ++ show-τ-Hs c t ++ " → " ++ show-τ-Hs c t₁ ++ ")"
  show-τ-Hs c (ty τ-Agda x) with Data.ForeignData.foreign-spec x
  show-τ-Hs c (ty τ-Agda x) | Data.HS x₁ UHC = x₁

  showSpec : ∀ {l} → {way : FFIWay} → ForeignSpec {l} way → Maybe String
  showSpec (HS_UHC x x₁) = just (x ++ " :: " ++ show-τ-Hs V.[] x₁)
