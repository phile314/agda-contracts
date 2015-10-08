module Foreign.Show where

open import Level
import Foreign.Base
open import Data.Maybe
open import Data.List as L hiding (_++_)
open import Data.String
open import Data.Nat

open Foreign.Base.FunImport
open import Reflection

module Fun where
  open import Data.Nat.Show as NS
  open import Category.Monad
  open import Category.Monad.Indexed
  open import Category.Applicative.Indexed
  open Foreign.Base
  open Category.Monad.Indexed.RawIMonad {Level.zero} {Level.zero} Data.Maybe.monad

  Γ : Set
  Γ = L.List String
  lookup : ∀ {a} {A : Set a} → ℕ → List A → Maybe A
  lookup n L.[] = nothing
  lookup ℕ.zero (x L.∷ xs) = just x
  lookup (ℕ.suc n) (x L.∷ xs) = lookup n xs

{-
  show-τ-Hs : ∀ {way} {n : ℕ} → Γ → τ-Hs way → Maybe String
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
  show-τ-Hs c (ty nm-Agda x) with x --with Data.ForeignData.foreign-spec x
  show-τ-Hs c (ty nm-Agda x) | Data.UHC-HS x₁ .nm-Agda = {!!}
  show-τ-Hs c (ty nm-Agda x) | Data.UHC-C x₁ .nm-Agda = {!!} -- just ("⟨" ++ showName nm-Agda ++ " as " ++ x₁ ++ "⟩")
-}
{-  showSpec : {way : FFIWay} → ForeignSpec way → Maybe String
  showSpec (HS-UHC x x₁) =
    show-τ-Hs {n = 0} L.[] x₁ >>= λ x₁' →
    return (x ++ " :: " ++ x₁')-}
