{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module Contracts.Base where

open import Data.List as List
open import Data.Nat
open import Data.Maybe


-- move to Agda stdlib
lookup : ∀ {A : Set} → ℕ → List A → Maybe A
lookup i [] = nothing
lookup ℕ.zero (x ∷ xs) = just x
lookup (ℕ.suc i) (x ∷ xs) = lookup i xs



open import Level
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat as N
open import Function


postulate OutOfBounds : ∀ {A : Set} → A
lookup' : ∀ {A : Set} → ℕ → List A → A
lookup' i xs with lookup i xs
lookup' i xs | just x = x
lookup' i xs | nothing = OutOfBounds


-- Conversion from A to B.
data Conversion (A : Set) (B : Set) : Set where
  total : (A → B) → Conversion A B
  withDec : (A → Dec B) → Conversion A B
  withMaybe : (A → Maybe B) → Conversion A B
  -- always failing conversion
  fail : Conversion A B


open import Data.Product

Conversions : Set → Set → Set
Conversions Aₜ Bₜ = Conversion Aₜ Bₜ × Conversion Bₜ Aₜ

record PartIso : Set where
  constructor mkPartIso
  field ARG-a : Set
        ARG-l : ARG-a → Set
        ARG-h : ARG-a → Set
        τ-l : (aa : ARG-a) → (ARG-l aa) → Set
        τ-h : (aa : ARG-a) → (ARG-h aa) → Set

        ⇅ : (aa : ARG-a) → (al : ARG-l aa) → (ah : ARG-h aa) → Conversions (τ-l aa al) (τ-h aa ah)

mkPartIso1 : (τₗ : Set) → (τₕ : Set) → Conversions τₗ τₕ → PartIso
mkPartIso1 τₗ τₕ ⇅ = mkPartIso ⊤ (λ _ → ⊤) (λ _ → ⊤) (λ _ _ → τₗ) (λ _ _ → τₕ) (λ _ _ _ → ⇅)
  where open import Data.Unit


open import Reflection

record PartIsoInt : Set where
  constructor mkIsoInt
  field wrapped : Term -- the part iso as term

open import Reflection

-- co-/contravariant context
data Context : Set where
  Pos : Context -- covariant
  Neg : Context -- contravariant

-- do we erase or not?
data ArgWay : Set where
  Keep : ArgWay
  Erase : ArgWay

invert : Context → Context
invert Pos = Neg
invert Neg = Pos

data InternalSyn : ℕ → Set where
  -- normal agda type, with at most n free vars
  agda-ty : ∀ {n} → Term → InternalSyn n
  π_∣_⇒_ : ∀ {n}
    → InternalSyn n -- type of the arg
    → ArgWay
    → InternalSyn (ℕ.suc n) -- body
    → InternalSyn n

  iso : ∀ {n}
    → (p : PartIsoInt)
    → Term -- ALL arguments - with env of all args
    → Term -- LOW arguments - with env of low args + all args
    → Term -- HIGH arguments - with env of high args + all args
    → InternalSyn n


def-argInfo : Arg-info
def-argInfo = arg-info visible relevant


private
  postulate
    InternalError : {a : Set} → a
    UnexpectedIsoInIsoArgs : {A : Set} → A

IsoHandler : Set
IsoHandler = (p : PartIsoInt)
  → Term -- ALL argument
  → Term -- LOW argument
  → Term -- HIGH argument
  → Term

private
  data TargetType : Set where
    Low High : TargetType

mkArg : Term → Arg Term
mkArg = arg (arg-info visible relevant)

getIsoLowType : IsoHandler
getIsoLowType p argₐ argₗ _ = def (quote PartIso.τ-l) (mkArg (PartIsoInt.wrapped p) ∷ mkArg argₐ ∷ mkArg argₗ ∷ [])

getIsoHighType : IsoHandler
getIsoHighType p argₐ _ argₕ = def (quote PartIso.τ-h) (mkArg (PartIsoInt.wrapped p) ∷ mkArg argₐ ∷ mkArg argₕ ∷ [])

elAGDA : ∀ {n} → Context → TargetType → (t : InternalSyn n) → Term
elArg : ∀ {n} → Context → TargetType → (t : InternalSyn n) → Arg Term

private
  unsafeFromJust : ∀ {a} → Maybe a → a
  unsafeFromJust (just x) = x
  unsafeFromJust nothing = InternalError

elAGDA ω ρ (agda-ty t) = t
elAGDA ω ρ (π  t ∣ k ⇒ t₁) = case (k , ω , ρ) of
  (λ { (Keep , _ , _) → keep
     ; (Erase , Pos , Low) → erase'
     ; (Erase , Pos , High) → keep
     ; (Erase , Neg , Low) → keep
     ; (Erase , Neg , High) → erase' })
  where
    keep = pi (arg def-argInfo (el unknown (elAGDA (invert ω) ρ t))) (abs "" (el unknown (elAGDA ω ρ t₁)))
    open import Reflection.DeBruijn as D
    erase' = unsafeFromJust (D.strengthen 1 (elAGDA ω ρ t₁))
elAGDA ω ρ (iso i argₐ argₗ argₕ) =
  case ρ of
    (λ { Low → getIsoLowType i argₐ argₗ argₕ
       ; High → getIsoHighType i argₐ argₗ argₕ })

elArg ω ρ t = arg def-argInfo (elAGDA ω ρ t)


deriveLowType : InternalSyn 0 → Term
deriveLowType t = elAGDA Pos Low t

deriveHighType : InternalSyn 0 → Term
deriveHighType t = elAGDA Pos High t


-- weaken the environment
wkΓ : ℕ → List ℕ → List ℕ
wkΓ k = List.map (N._+_ k)

open import Data.String

private
  postulate
    conversionFailure : {A : Set} → String → A

-- Unsafe conversion primitive
↯ : (A : Set) (B : Set) → Conversion A B → A → B
↯ _ _ (total x) x₁ = x x₁
↯ _ _ (withDec x) x₁ with x x₁
↯ _ _ (withDec x) x₁ | yes p = p
↯ _ _ (withDec x) x₁ | no ¬p = conversionFailure ""
↯ _ _ (withMaybe x) x₁ with x x₁
↯ _ _ (withMaybe x) x₁ | just x₂ = x₂
↯ _ _ (withMaybe x) x₁ | nothing = conversionFailure ""
↯ _ _ fail x = conversionFailure ""


import Data.Bool as B
open import Relation.Nullary.Decidable

lett_inn_ : Term → Term → Term
lett_inn_ (var x []) t₂ = subst [ safe (var x []) _ ] t₂
  where open import Reflection.Substitute
lett_inn_ t₁ t₂ = def (quote _$_)
          ( arg def-argInfo (lam visible (abs "" t₂))
          ∷ arg def-argInfo t₁
          ∷ [])

app : Term → Term → Term
app t₁ t₂ = def (quote _$_)
          ( arg def-argInfo t₁
          ∷ arg def-argInfo t₂
          ∷ [])

up : (p : PartIso) → (aa : PartIso.ARG-a p) → (al : PartIso.ARG-l p aa) → (ah : PartIso.ARG-h p aa)
  → PartIso.τ-l p aa al → PartIso.τ-h p aa ah
up p aa al ah from = ↯ _ _ (proj₁ $ PartIso.⇅ p aa al ah) from

down : (p : PartIso) → (aa : PartIso.ARG-a p) → (al : PartIso.ARG-l p aa) → (ah : PartIso.ARG-h p aa)
  → PartIso.τ-h p aa ah → PartIso.τ-l p aa al
down p aa al ah from = ↯ _ _ (proj₂ $ PartIso.⇅ p aa al ah) from


contract-apply1 : ∀ {n}
  → (fde : InternalSyn n)
  → Term -- thing to wrap
  → Context -- seems to be only used to figure out in which directin to convert
  → List ℕ -- environment
  → Term
contract-apply1 (agda-ty _) wr ω Γ = wr
contract-apply1 {n} (π fde ∣ k ⇒ fde₁) wr ω Γ =
  lam visible (abs "x" bd)
  where open import Reflection.DeBruijn
        ls = contract-apply1 fde (var 0 []) (invert ω) (wkΓ 1 Γ)
        toWrap = case k of
          λ { Keep → app (weaken 2 wr) (var 0 [])
            ; Discard → weaken 2 wr
            }
        rs = contract-apply1 fde₁ toWrap ω (0 ∷ wkΓ 2 Γ)
        bd = lett ls inn rs
contract-apply1 (iso {n} x argₐ argₗ argₕ) wr ω Γ =
  -- extract the conversion from the named iso
  -- apply unsafeConvert
  def (convFun ω) ((mkArg $ PartIsoInt.wrapped x) ∷ argₐ' ∷ argₗ' ∷ argₕ' ∷ mkArg wr ∷ [])
  where
        open import Reflection.Substitute
        ix = reverse $ downFrom (List.length Γ)
        s = subst (List.map (λ ix → safe (var ix []) _) Γ)

        mkArg' = mkArg

        idEnv = reverse $ downFrom n
        -- this only refers to arguments which do not have any isomorphisms in them
        -- so we can return the wrapped or the original term
        argₐ' = mkArg $ subst (List.map (λ x → safe (var (x N.+ 1) []) _) Γ) argₐ
        -- this only refers to low args. Use the original lambda term
        argₗ' = mkArg $ subst (List.map (λ x → safe (var (x N.+ 1) []) _) Γ) argₗ
        -- this only refers to high args. Use the wrapped term.
        argₕ' = mkArg $ subst (List.map (λ x → safe (var x []) _) Γ) argₕ

        convFun : Context → Name
        convFun Pos = quote up
        convFun Neg = quote down


-- produces the wrapper for lifting the low term to the high type
contract-apply : (fde : InternalSyn 0) → Term {- low term / function -} → Term
contract-apply fde low  = contract-apply1 fde low Pos []

open import Level


toIntPartIso : PartIso
  → Term
  → PartIsoInt
toIntPartIso p pₙ = record
  { wrapped = pₙ
  }



