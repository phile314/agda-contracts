{-# OPTIONS --no-termination-check #-}

module Contracts.Base where

open import Data.List as List
open import Data.Nat
open import Data.Maybe
-- TODO move to stdlib
lookup : ∀ {a} {A : Set a} → ℕ → List A → Maybe A
lookup i [] = nothing
lookup ℕ.zero (x ∷ xs) = just x
lookup (ℕ.suc i) (x ∷ xs) = lookup i xs



open import Level
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat as N
open import Function


postulate OutOfBounds : ∀ {a} {A : Set a} → A
lookup' : ∀ {a} {A : Set a} → ℕ → List A → A
lookup' i xs with lookup i xs
lookup' i xs | just x = x
lookup' i xs | nothing = OutOfBounds


data Conversion {a b} (A : Set a) (B : Set b) : Set (Level.suc (a Level.⊔ b)) where
  total : (A → B) → Conversion A B
  withDec : (A → Dec B) → Conversion A B
  withMaybe : (A → Maybe B) → Conversion A B
  fail : Conversion A B

ArgTys : ∀ {l} → Set (Level.suc l)
ArgTys {l} = List (Set l)

-- if we want dependent args, we could make WithArgs into a dependent list (chained Σ)
data WithArgs {l} : (ArgTys {l}) → Set l where
  [] : WithArgs []
  _,_ : {A : Set l} → (a : A) → {AS : ArgTys} → WithArgs AS → WithArgs (A List.∷ AS)

argsToTy : ∀ {b} → ArgTys {b} → Set b → Set (b)
argsToTy {b} [] f = f
argsToTy {b} (x List.∷ a) f = x → argsToTy {b} a f

open import Data.Product


open import Reflection

Conversions : ∀ {l} → Set l → Set l → Set (Level.suc l)
Conversions Aₜ Bₜ = Conversion Aₜ Bₜ × Conversion Bₜ Aₜ

record PartIso {l} : Set (Level.suc (Level.suc l)) where
  constructor mkPartIso
  field LOWₐ : ArgTys {Level.suc l} -- this are the common arguments
        HIGHₐ : ArgTys {Level.suc l} -- agda only arguments
        iso : argsToTy LOWₐ (Σ (Set l) (λ HSₜ →
                       argsToTy HIGHₐ (Σ (Set l) (Conversions HSₜ))))

record PartIsoInt {l} : Set (Level.suc (Level.suc l)) where
  field wrapped : PartIso {l}
        wrappedₙ : Name -- name of the part iso

applyArgs : ∀ {l} → {aTys : ArgTys {l}} {A : Set l} → (f : argsToTy aTys A) → WithArgs aTys → A
applyArgs {aTys = []} f [] = f
applyArgs {aTys = A₁ ∷ aTys} f (a , args) = applyArgs (f a) args


open import Data.Fin
open import Reflection

data Position : Set where
  Pos : Position
  Neg : Position

invertPosition : Position → Position
invertPosition Pos = Neg
invertPosition Neg = Pos

import Data.Vec as V

-- TODO discard only makes sense in negative positions, we should enforce that it is only specified there
data T {l} : ℕ → Set (Level.suc (Level.suc l)) where
  set : ∀ {n} → (l : ℕ) → T n
  -- var
  var_∙_ : ∀ {n}
    → (k : Fin n)
    → List (T {l} n) -- arguments, we don't support keeping the arguments anyway, so just force discard here.
    → T n
  def_∙_ : ∀ {n}
    → (nm : Name)
    → List (T {l} n)
    → T n
  π_⇒_ : ∀ {n}
    → T {l} n -- type of the arg
    → T {l} (ℕ.suc n) -- body
    → T {_} n

  iso : ∀ {n}
    → (p : PartIsoInt {l})
    → V.Vec (T {l} n) (length (PartIso.LOWₐ (PartIsoInt.wrapped p))) -- LOW arguments
    → V.Vec (T {l} n) (length (PartIso.HIGHₐ (PartIsoInt.wrapped p))) -- HIGH arguments
    → T n


def-argInfo : Arg-info
def-argInfo = arg-info visible relevant

partIsoLowTy : ∀ {l} → (p : PartIso {l}) → WithArgs (PartIso.LOWₐ p) → Set l
partIsoLowTy p args = proj₁ (applyArgs (PartIso.iso p) args)


postulate
  error : {a : Set} → a
  error2 : {a : Set} → a
  notImpl : {a : Set} → a
  UnexpectedIsoInIsoArgs : ∀ {a} {A : Set a} → A

IsoHandler : ∀ {l} → Set (Level.suc (Level.suc l))
IsoHandler {l} = {n : ℕ} → (p : PartIsoInt {l})
  → V.Vec (T {l} n) (length (PartIso.LOWₐ (PartIsoInt.wrapped p))) -- LOW arguments
  → V.Vec (T {l} n) (length (PartIso.HIGHₐ (PartIsoInt.wrapped p))) -- HIGH arguments
  → Term


elAGDA : ∀ {l n} → IsoHandler {l} → (t : T {l} n) → Term
elArg : ∀ {l n} → IsoHandler {l} → (t : T {l} n) → Arg Term

elAGDA h (var k ∙ xs) = var (toℕ k) (List.map (elArg h) xs)
elAGDA h (def x ∙ xs) = def x (List.map (elArg h) xs)
elAGDA h (π  t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA h t))) (abs "" (el unknown (elAGDA h t₁)))
elAGDA h (set l) = sort (lit l)
elAGDA h (iso i HSₐ AGDAₐ) = h i HSₐ AGDAₐ

elArg h t = arg def-argInfo (elAGDA h t)


mkArgs : ∀ {l n} → (as : ArgTys {Level.suc l}) → V.Vec (T {l} n) (length as) → Term
mkArgs [] V.[] = con (quote WithArgs.[]) []
mkArgs (x ∷ as₁) (x₁ V.∷ ts) = con (quote WithArgs._,_)
  ( arg def-argInfo
    (con (quote Level.lift)
      [ arg def-argInfo (elAGDA UnexpectedIsoInIsoArgs x₁) ]
    )
  ∷ arg def-argInfo (mkArgs as₁ ts)
  ∷ [])


getIsoLow : ∀ {l n}
  → (p : PartIsoInt {l})
  → V.Vec (T {l} n) (length (PartIso.LOWₐ (PartIsoInt.wrapped p))) -- LOW Args
  → Term
getIsoLow p as =
  def (quote applyArgs)
    (arg def-argInfo (tiso)
    ∷ (arg def-argInfo (mkArgs atys as))
    ∷ [])
  where
    tiso = def (quote PartIso.iso)
      [ arg def-argInfo (def (PartIsoInt.wrappedₙ p) [] ) ]
    atys = PartIso.LOWₐ (PartIsoInt.wrapped p)

-- gets the iso high pair
getIsoHigh : ∀ {l n}
  → Term -- the term representing ISO Low
  → (p : PartIsoInt {l})
  → V.Vec (T {l} n) (length (PartIso.HIGHₐ (PartIsoInt.wrapped p))) -- HIGH Args
  → Term
getIsoHigh lw p as =
  def (quote applyArgs)
    (arg def-argInfo high
    ∷ arg def-argInfo (mkArgs atys as)
    ∷ [])
  where
    atys = PartIso.HIGHₐ (PartIsoInt.wrapped p)
    high = def (quote proj₂) [ arg def-argInfo lw ]

getIsoLowType : ∀ {l} → IsoHandler {l}
getIsoLowType p LOWₐ HIGHₐ = def (quote proj₁)
  [ arg def-argInfo (getIsoLow p LOWₐ ) ]

getAgdaLowType : ∀ {l} → T {l} 0 → Term
getAgdaLowType t = elAGDA getIsoLowType t

getAgdaHighType : ∀ {l} → T {l} 0 → Term
getAgdaHighType t = elAGDA handleIso t
  where
    handleIso : IsoHandler
    handleIso p LOWₐ HIGHₐ =
      let low = getIsoLow p LOWₐ
       in def (quote proj₁)
            [ arg def-argInfo (getIsoHigh low p HIGHₐ) ]

shift : ℕ → List ℕ → List ℕ
shift k = List.map (N._+_ k)

open import Data.String
postulate
  conversionFailure : ∀ {a} → {A : Set a} → String → A

unsafeConvert : {a b : Level} (A : Set a) (B : Set b) → Conversion A B → A → B
unsafeConvert _ _ (total x) x₁ = x x₁
unsafeConvert _ _ (withDec x) x₁ with x x₁
unsafeConvert _ _ (withDec x) x₁ | yes p = p
unsafeConvert _ _ (withDec x) x₁ | no ¬p = conversionFailure ""
unsafeConvert _ _ (withMaybe x) x₁ with x x₁
unsafeConvert _ _ (withMaybe x) x₁ | just x₂ = x₂
unsafeConvert _ _ (withMaybe x) x₁ | nothing = conversionFailure ""
unsafeConvert _ _ fail x = conversionFailure ""


mkArg : ℕ → Arg Term
mkArg i = arg (arg-info visible relevant) (var i [])

-- substitution
subst : (ℕ → ℕ) -- substitution function
  → Term
  → Term
substArgs : (ℕ → ℕ) → Arg Term → Arg Term

-- substitute free variables
subst σ (var x args) = var (σ x) (List.map (substArgs σ) args)
subst σ (con c args) = con c (List.map (substArgs σ) args)
subst σ (def f args) = def f (List.map (substArgs σ) args)
subst σ (lam v (abs x t)) = lam v (abs x (subst σ' t))
  where
    σ' : ℕ → ℕ
    σ' ℕ.zero = ℕ.zero -- the given var is not free, so just return it unchanged
    σ' (ℕ.suc i) = ℕ.suc (σ i)
subst σ (pat-lam cs args) = notImpl
subst σ (pi t₁ t₂) = notImpl
subst σ (sort s) = notImpl
subst σ (lit l) = notImpl
subst σ (quote-goal t) = notImpl
subst σ (quote-term t) = notImpl
subst σ quote-context = notImpl
subst σ (unquote-term t args) = notImpl
subst σ unknown = notImpl

substArgs σ (arg i x) = arg i (subst σ x)

import Data.Bool as B
open import Relation.Nullary.Decidable

lett_inn_ : Term → Term → Term
lett_inn_ (var x []) t₂ = subst (λ x₁ → B.if ⌊ x₁ N.≟ 0 ⌋ then x else x₁ ∸ 1) t₂
lett_inn_ t₁ t₂ = def (quote _$_)
          ( arg def-argInfo (lam visible (abs "" t₂))
          ∷ arg def-argInfo t₁
          ∷ [])

ffi-lift1 : ∀ {l n}
  → (fde : T {l} n)
  → (List ℕ → Term) -- thing to wrap
  → Position -- seems to be only used to figure out in which directin to convert
  → List ℕ -- environment
  → Term
ffi-lift1 (set l₁) wr pos Γ = wr Γ
ffi-lift1 (var k ∙ x) wr pos Γ = wr Γ
ffi-lift1 (def nm ∙ x) wr pos Γ  = wr Γ
ffi-lift1 {_} {n} (π fde ⇒ fde₁) wr pos Γ =
  lam visible (abs "x" bd)
  where ls = ffi-lift1 fde (λ env → let nVars = length env ∸ length Γ
           -- TODO should we really apply the whole new env here?
           in var (nVars * 2) (List.map mkArg (reverse (take nVars env)))) (invertPosition pos) (shift 1 Γ)
        rs = ffi-lift1 fde₁ wr pos (0 ∷ shift 2 Γ)
        bd = lett ls inn rs
ffi-lift1 (iso {l} x LOWₐ HIGHₐ) wr pos Γ =
  -- extract the conversion from the named iso
  -- apply unsafeConvert
  def (quote unsafeConvert)
    ( arg def-argInfo (tyFrom pos)
    ∷ arg def-argInfo (tyTo pos)
    ∷ arg def-argInfo conv
    ∷ arg def-argInfo (wr Γ) ∷ [])
  where
        s = subst (λ x → lookup' x Γ)
        
        getConv : Position → Term → Term
        getConv Pos t = (def (quote proj₁) [ arg def-argInfo t ]) 
        getConv Neg t = (def (quote proj₂) [ arg def-argInfo t ])
        
        isoLow : Term
        isoLow = getIsoLow x LOWₐ
        isoHigh : Term
        isoHigh = getIsoHigh isoLow x HIGHₐ
        
        tyLow = s $ def (quote proj₁) [ arg def-argInfo isoLow ]
        tyHigh = s $ def (quote proj₁) [ arg def-argInfo isoHigh ]
        tyFrom : Position → Term
        tyFrom Pos = tyLow
        tyFrom Neg = tyHigh
        tyTo : Position → Term
        tyTo Pos = tyHigh
        tyTo Neg = tyLow

        conv : Term
        conv = s $ getConv pos (def (quote proj₂) [ arg def-argInfo isoHigh ])

ffi-lift : ∀ {l} → (fde : T {l} 0) → Name {- name of the low level fun -} → Term
ffi-lift fde nm  = ffi-lift1 fde (λ Γ → def nm (List.map mkArg (List.reverse Γ))) Pos []

open import Level


toIntPartIso : ∀ {l}
  → PartIso {l}
  → Name --part iso name
  → PartIsoInt
toIntPartIso p pₙ = record
  { wrapped = p
  ; wrappedₙ = pₙ
  }
