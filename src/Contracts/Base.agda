{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module Contracts.Base where

open import Data.List as List
open import Data.Nat
open import Data.Maybe

-- TODO move to stdlib
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
  field ARGₐ : Set
        ARGₗ : ARGₐ → Set
        ARGₕ : ARGₐ → Set
        τₗ : (aa : ARGₐ) → (ARGₗ aa) → Set
        τₕ : (aa : ARGₐ) → (ARGₕ aa) → Set

        ⇅ : (aa : ARGₐ) → (al : ARGₗ aa) → (ah : ARGₕ aa) → Conversions (τₗ aa al) (τₕ aa ah)

mkPartIso1 : (τₗ : Set) → (τₕ : Set) → Conversions τₗ τₕ → PartIso
mkPartIso1 τₗ τₕ ⇅ = mkPartIso ⊤ (λ _ → ⊤) (λ _ → ⊤) (λ _ _ → τₗ) (λ _ _ → τₕ) (λ _ _ _ → ⇅)
  where open import Data.Unit


open import Reflection

record PartIsoInt : Set where
  constructor mkIsoInt
  field wrapped : Term -- the part iso as term


open import Data.Fin
open import Reflection

data Position : Set where
  Pos : Position
  Neg : Position

data ArgWay : Set where
  Keep : ArgWay
  Erase : ArgWay

invertPosition : Position → Position
invertPosition Pos = Neg
invertPosition Neg = Pos

import Data.Vec as V

data T : ℕ → Set where
  -- normal agda type, with at most n free vars
  agda-ty : ∀ {n} → Term → T n
  π_∣_⇒_ : ∀ {n}
    → T n -- type of the arg
    → ArgWay
    → T (ℕ.suc n) -- body
    → T n

  iso : ∀ {n}
    → (p : PartIsoInt)
    → Term -- ALL arguments - with env of all args
    → Term -- LOW arguments - with env of low args + all args
    → Term -- HIGH arguments - with env of high args + all args
    → T n


def-argInfo : Arg-info
def-argInfo = arg-info visible relevant


private
  postulate
    InternalError : {a : Set} → a
    error : {a : Set} → a
    error2 : {a : Set} → a
    notImpl notImpl2 notImpl3 : {a : Set} → a
    UnexpectedIsoInIsoArgs : {A : Set} → A

open import Data.Bool hiding (T)

IsoHandler : Set
IsoHandler = (p : PartIsoInt)
  → Term -- ALL argument
  → Term -- LOW argument
  → Term -- HIGH argument
  → Term

record elOpts : Set where
  constructor mkElOpts
  field isoHandler : IsoHandler
        ignoreDiscard : Bool

-- todo handle discard in neg. position properly
elAGDA : ∀ {n} → elOpts → (t : T n) → Term
elArg : ∀ {n} → elOpts → (t : T n) → Arg Term

private
  unsafeFromJust : ∀ {a} → Maybe a → a
  unsafeFromJust (just x) = x
  unsafeFromJust nothing = InternalError

-- Also, t may only have n free vars I think!
elAGDA h (agda-ty t) = t
elAGDA h (π  t ∣ k ⇒ t₁) = case k of
  (λ { Keep → r-keep
     ; Discard → if elOpts.ignoreDiscard h
         then r-keep
         else (unsafeFromJust (D.strengthen 1 (elAGDA h t₁)))
     })
  where
    r-keep = pi (arg def-argInfo (el unknown (elAGDA h t))) (abs "" (el unknown (elAGDA h t₁)))
    open import Reflection.DeBruijn as D
elAGDA h (iso i argₐ argₗ argₕ) = (elOpts.isoHandler h) i argₐ argₗ argₕ

elArg h t = arg def-argInfo (elAGDA h t)


mkArg : Term → Arg Term
mkArg = arg (arg-info visible relevant)

getIsoLowType : IsoHandler
getIsoLowType p argₐ argₗ _ = def (quote PartIso.τₗ) (mkArg (PartIsoInt.wrapped p) ∷ mkArg argₐ ∷ mkArg argₗ ∷ [])

getIsoHighType : IsoHandler
getIsoHighType p argₐ _ argₕ = def (quote PartIso.τₕ) (mkArg (PartIsoInt.wrapped p) ∷ mkArg argₐ ∷ mkArg argₕ ∷ [])


deriveLowType : T 0 → Term
deriveLowType t = elAGDA (mkElOpts getIsoLowType false) t

deriveHighType : T 0 → Term
deriveHighType t = elAGDA (mkElOpts getIsoHighType true) t


shift : ℕ → List ℕ → List ℕ
shift k = List.map (N._+_ k)

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

up : (p : PartIso) → (aa : PartIso.ARGₐ p) → (al : PartIso.ARGₗ p aa) → (ah : PartIso.ARGₕ p aa)
  → PartIso.τₗ p aa al → PartIso.τₕ p aa ah
up p aa al ah from = ↯ _ _ (proj₁ $ PartIso.⇅ p aa al ah) from

down : (p : PartIso) → (aa : PartIso.ARGₐ p) → (al : PartIso.ARGₗ p aa) → (ah : PartIso.ARGₕ p aa)
  → PartIso.τₕ p aa ah → PartIso.τₗ p aa al
down p aa al ah from = ↯ _ _ (proj₂ $ PartIso.⇅ p aa al ah) from


contract-apply1 : ∀ {n}
  → (fde : T n)
  → Term -- thing to wrap
  → Position -- seems to be only used to figure out in which directin to convert
  → List ℕ -- environment
  → Term
contract-apply1 (agda-ty _) wr pos Γ = wr
contract-apply1 {n} (π fde ∣ k ⇒ fde₁) wr pos Γ =
  lam visible (abs "x" bd)
  where open import Reflection.DeBruijn
        ls = contract-apply1 fde (var 0 []) (invertPosition pos) (shift 1 Γ)
        toWrap = case k of
          λ { Keep → app (weaken 2 wr) (var 0 [])
            ; Discard → weaken 2 wr
            }
        rs = contract-apply1 fde₁ toWrap pos (0 ∷ shift 2 Γ)
        bd = lett ls inn rs
contract-apply1 (iso {n} x argₐ argₗ argₕ) wr pos Γ =
  -- extract the conversion from the named iso
  -- apply unsafeConvert
  def (convFun pos) ((mkArg $ PartIsoInt.wrapped x) ∷ argₐ' ∷ argₗ' ∷ argₕ' ∷ mkArg wr ∷ [])
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

        convFun : Position → Name
        convFun Pos = quote up
        convFun Neg = quote down


-- produces the wrapper for lifting the low term to the high type
contract-apply : (fde : T 0) → Term {- low term / function -} → Term
contract-apply fde low  = contract-apply1 fde low Pos []

open import Level


toIntPartIso : PartIso
  → Term
  → PartIsoInt
toIntPartIso p pₙ = record
  { wrapped = pₙ
  }



