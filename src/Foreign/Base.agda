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
  data τ-Hs {way : FFIWay} : Set where
    var : (k : ℕ) → τ-Hs
    app : (τ-Hs {way = way}) → (τ-Hs {way = way}) → τ-Hs
    ∀'  : (τ-Hs {way = way}) → τ-Hs
    _⇒_ : (τ-Hs {way = way}) → (τ-Hs {way = way}) → τ-Hs
    ty  : (nm-Agda : Name) → {{foreign : Data.ForeignData way nm-Agda}} → τ-Hs

  data ForeignSpec : FFIWay → Set where
    HS-UHC : HS-UHC-EntityName → τ-Hs {HS-UHC} → ForeignSpec HS-UHC

  record ForeignFun (way : FFIWay) : Set where
    field foreign-spec : ForeignSpec way

  open import Data.List using (List; foldl)
  apps : ∀ {way} → (τ-Hs {way = way}) → List (τ-Hs {way = way}) → τ-Hs {way = way}
  apps f xs = foldl app f xs

  import Data.List as L
  import Data.Vec as V
  open import Data.Maybe
  import Data.Nat.Show as NS

  open import Category.Monad
  open import Category.Monad.Indexed
  open import Category.Applicative.Indexed
  open Category.Monad.Indexed.RawIMonad {Level.zero} {Level.zero} Data.Maybe.monad

  Γ : Set
  Γ = L.List String
  lookup : ∀ {a} {A : Set a} → ℕ → List A → Maybe A
  lookup n L.[] = nothing
  lookup ℕ.zero (x L.∷ xs) = just x
  lookup (ℕ.suc n) (x L.∷ xs) = lookup n xs

  show-τ-Hs : ∀ {way} {n : ℕ} → Γ → (τ-Hs {way}) → Maybe String
  show-τ-Hs c (var x) = lookup x c
  show-τ-Hs {_} {n} c (app t t₁) =
    show-τ-Hs {n = n} c t >>= λ t' →
    show-τ-Hs {n = n} c t₁ >>= λ t₁' →
    return ("(" ++ t' ++ " " ++ t₁' ++ ")")
  show-τ-Hs {_} {n} c (∀' t) =
    show-τ-Hs {n = ℕ.suc n} (nm L.∷ c) t >>= λ t' →
    return ("(∀ " ++ nm ++ " . " ++ t' ++ ")")
    where nm = "a" ++ NS.show n
  show-τ-Hs {_} {n} c (t ⇒ t₁) =
    show-τ-Hs {n = n} c t >>= λ t' →
    show-τ-Hs {n = n} c t₁ >>= λ t₁' →
    return ("(" ++ t' ++ " → " ++ t₁' ++ ")")
  show-τ-Hs c (ty nm-Agda {{x}}) with Data.ForeignData.foreign-spec x
  show-τ-Hs c (ty nm-Agda {{x}}) | Data.HS-UHC x₁ = just ("⟨" ++ showName nm-Agda ++ " as " ++ x₁ ++ "⟩")

  showSpec : {way : FFIWay} → ForeignSpec way → Maybe String
  showSpec (HS-UHC x x₁) =
    show-τ-Hs {n = 0} L.[] x₁ >>= λ x₁' →
    return (x ++ " :: " ++ x₁')
