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


data Conversion (A : Set) (B : Set) : Set where
  total : (A → B) → Conversion A B
  withDec : (A → Dec B) → Conversion A B
  withMaybe : (A → Maybe B) → Conversion A B
  fail : Conversion A B


open import Data.Sum
open import Data.Product


-- we only care about top-level args!
data ArgTys : Set where
  _A⇒_ : (A : Set) → (A → ArgTys) → ArgTys
  A∎ : ArgTys

_A⇒'_ : Set → ArgTys → ArgTys
(x A⇒' y) = x A⇒ (λ _ → y)

elA : ArgTys → Set → Set
elA (A A⇒ B) f = (a : A) → elA (B a) f
elA A∎ f = f


-- if we want dependent args, we could make WithArgs into a dependent list (chained Σ)
data WithArgs : ArgTys → Set where
  _W⇒_ : {A : Set} → (a : A) → {B : A → ArgTys} → WithArgs (B a) → WithArgs (A A⇒ B)
  W∎ : WithArgs A∎

_+A+_ : ArgTys → ArgTys → ArgTys
(A A⇒ B) +A+ x = A A⇒ (λ a → B a +A+ x)
A∎ +A+ x = x

{-argsToTy : ArgTys → Set
argsToTy (x A⇒ x₁) = (a : argsToTy x) → argsToTy {!x₁ a!}
argsToTy (A∎ x) = x-}

--[] f = f
--argsToTy (x List.∷ a) f = x → argsToTy a f

open import Data.Product


open import Reflection

LOW-τ = Set
HIGH-τ = Set

Conversions : Set → Set → Set
Conversions Aₜ Bₜ = Conversion Aₜ Bₜ × Conversion Bₜ Aₜ

record PartIso' (LOWₐ : ArgTys) (HIGHₐ : ArgTys) : Set where
  field
    LOW : WithArgs LOWₐ → Set
    HIGH : WithArgs HIGHₐ → Set
    conv : (l : WithArgs LOWₐ) → (h : WithArgs HIGHₐ) → Conversions (LOW l) (HIGH h)

record PartIso : Set where
  constructor mkPartIso
  field
    ALLₐ : ArgTys
    iso : WithArgs ALLₐ → (Σ (ArgTys × ArgTys) (λ as → PartIso' (proj₁ as) (proj₂ as)))
    

record PartIsoInt : Set where
  constructor mkIsoInt
  field wrappedₙ : Term --Name -- name of the part iso
--  field wrapped : Term

applyArgs : {aTys : ArgTys} {A : Set} → (f : elA aTys A) → WithArgs aTys → A
applyArgs {aTys A⇒ x} f (a W⇒ x₁) = applyArgs (f a) x₁
applyArgs {A∎} f W∎ = f


open import Data.Fin
open import Reflection

data Position : Set where
  Pos : Position
  Neg : Position

data ArgWay : Set where
  Keep : ArgWay
  Discard : ArgWay

invertPosition : Position → Position
invertPosition Pos = Neg
invertPosition Neg = Pos

import Data.Vec as V

data Shape : Position → Set where
  S∎ : ∀ {p} → Shape p
  _S⇒_ : ∀ {p} → Shape (invertPosition p) → Shape p → Shape p


data C : {p : Position} → Shape p → Set
elC : ∀ {p} {sh : Shape p} → C sh → Set

{-k : ∀ {P} → ArgWay → C (invertPosition P) → Set
k {P = P} Keep c = elC c → C P
k {P = Pos} Discard c = C Pos × (elC c → C Pos)
k {P = Neg} Discard c = C Neg × (elC c → C Neg)-}

data C  where
  --normal type (List, Nat, Set)
  ⟦C_⟧ : ∀ {p} → Set → C (S∎ {p})
  -- pi type
  _C⇒_ : ∀ {p} {sh-a : Shape (invertPosition p)} {sh-b : Shape p} → (c : C sh-a) → (aw : ArgWay)
    → (elC c → C sh-b)
    → C (sh-a S⇒ sh-b)

elC ⟦C x ⟧ = x
elC (_C⇒_ c aw x) = (a : elC c) → elC (x a)

CT : Position → Set
CT p = Σ (Shape p) (λ shape → C shape × C shape × C shape)

_⇒_ : ∀ {p} → CT (invertPosition p) → CT p → CT p
(sh₁ , low₁ , high₁ , conv₁) ⇒ (sh₂ , low₂ , high₂ , conv₂) = (sh₁ S⇒ sh₂) , ((conv₁ C⇒ Keep) (λ _ → conv₂) , {!!})

-- TODO discard only makes sense in negative positions, we should enforce that it is only specified there
data T : ℕ → Set where
  set : ∀ {n} → (l : ℕ ) → T n
  -- var
  var_∙_ : ∀ {n}
    → (k : Fin n)
    → List (T n) -- arguments, we don't support keeping the arguments anyway, so just force discard here.
    → T n
  def_∙_ : ∀ {n}
    → (nm : Name)
    → List (T n)
    → T n
  π_∣_⇒_ : ∀ {n}
    → T n -- type of the arg
    → ArgWay
    → T (ℕ.suc n) -- body
    → T n

  iso : ∀ {n}
    → (p : PartIsoInt)
    → List (T n) -- LOW arguments
    → List (T n) -- HIGH arguments
    → T n


def-argInfo : Arg-info
def-argInfo = arg-info visible relevant

{-partIsoLowTy : (p : PartIso) → WithArgs (PartIso.LOWₐ p) → Set
partIsoLowTy p args = proj₁ (proj₁ (applyArgs (PartIso.iso p) args))


postulate
  error : {a : Set} → a
  error2 : {a : Set} → a
  notImpl notImpl2 notImpl3 : {a : Set} → a
  UnexpectedIsoInIsoArgs : {A : Set} → A

open import Data.Bool hiding (T)

IsoHandler : Set
IsoHandler = {n : ℕ} → (p : PartIsoInt)
  → List (T n) -- LOW arguments
  → List (T n) -- HIGH arguments
  → Term

record elOpts : Set where
  constructor mkElOpts
  field isoHandler : IsoHandler
        ignoreDiscard : Bool

-- todo handle discard in neg. position properly
elAGDA : ∀ {n} → elOpts → (t : T n) → Term
elArg : ∀ {n} → elOpts → (t : T n) → Arg Term

elAGDA h (var k ∙ xs) = var (toℕ k) (List.map (elArg h) xs)
elAGDA h (def x ∙ xs) = def x (List.map (elArg h) xs)
elAGDA h (π  t ∣ k ⇒ t₁) = case k of
  (λ { Keep → r-keep
     ; Discard → if elOpts.ignoreDiscard h then r-keep else elAGDA h t₁
     })
  where r-keep = pi (arg def-argInfo (el unknown (elAGDA h t))) (abs "" (el unknown (elAGDA h t₁)))
elAGDA h (set l) = sort (lit l) -- we use type-in-type, so what should we do here?
elAGDA h (iso i HSₐ AGDAₐ) = (elOpts.isoHandler h) i HSₐ AGDAₐ

elArg h t = arg def-argInfo (elAGDA h t)


mkArgs : ∀ {n} → List (T n) → Term
mkArgs [] = con (quote WithArgs.W∎) []
mkArgs (x₁ ∷ ts) = con (quote WithArgs._W⇒_)
  ( arg def-argInfo
--    (con (quote Level.lift)
--     [ arg def-argInfo (elAGDA UnexpectedIsoInIsoArgs x₁) ]
     (elAGDA UnexpectedIsoInIsoArgs x₁)
--    )
  ∷ arg def-argInfo (mkArgs ts)
  ∷ [])


getIsoLow : ∀ {n}
  → (p : PartIsoInt)
  → List (T n) -- LOW Args
  → Term
getIsoLow p as =
  def (quote applyArgs)
    (arg def-argInfo (tiso)
    ∷ (arg def-argInfo (mkArgs as))
    ∷ [])
  where
    tiso = def (quote PartIso.iso)
      [ arg def-argInfo (PartIsoInt.wrappedₙ p)  ]

-- gets the iso high pair
getIsoHigh : ∀ {n}
  → Term -- the term representing ISO Low
  → (p : PartIsoInt)
  → List (T n) -- HIGH Args
  → Term
getIsoHigh lw p as =
  def (quote applyArgs)
    (arg def-argInfo high
    ∷ arg def-argInfo (mkArgs as)
    ∷ [])
  where
    high = def (quote proj₂) [ arg def-argInfo lw ]

getIsoLowType : IsoHandler
getIsoLowType p LOWₐ HIGHₐ = def (quote proj₁)
  [ arg def-argInfo (getIsoLow p LOWₐ ) ]

getAgdaLowType : T 0 → Term
getAgdaLowType t = elAGDA (mkElOpts getIsoLowType false) t

getAgdaHighType : T 0 → Term
getAgdaHighType t = elAGDA (mkElOpts handleIso true) t
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
  conversionFailure : {A : Set} → String → A

unsafeConvert : (A : Set) (B : Set) → Conversion A B → A → B
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


-- substitution for free variables
subst : (ℕ → ℕ) -- substitution function
  → Term
  → Term
substArgs : (ℕ → ℕ) → Arg Term → Arg Term
substCl : Clause → Clause
substSort : (ℕ → ℕ) → Sort → Sort

subst σ (var x args) = var (σ x) (List.map (substArgs σ) args)
subst σ (con c args) = con c (List.map (substArgs σ) args)
subst σ (def f args) = def f (List.map (substArgs σ) args)
subst σ (lam v (abs x t)) = lam v (abs x (subst σ' t))
  where
    σ' : ℕ → ℕ
    σ' ℕ.zero = ℕ.zero -- the given var is not free, so just return it unchanged
    σ' (ℕ.suc i) = ℕ.suc (σ i)
subst σ (pat-lam cs args) = pat-lam (List.map substCl cs) (List.map (substArgs σ) args)
subst σ (pi t₁ t₂) = notImpl2
subst σ (sort s) = sort (substSort σ s)
subst σ (lit l) = lit l
subst σ (quote-goal t) = notImpl3
subst σ (quote-term t) = notImpl3
subst σ quote-context = quote-context
subst σ (unquote-term t args) = notImpl3
subst σ unknown = unknown

substArgs σ (arg i x) = arg i (subst σ x)

substCl (clause pats body) = notImpl3
substCl (absurd-clause pats) = absurd-clause pats

substSort σ (set t) = set (subst σ t)
substSort σ (lit n) = lit n
substSort σ unknown = unknown


import Data.Bool as B
open import Relation.Nullary.Decidable

lett_inn_ : Term → Term → Term
lett_inn_ (var x []) t₂ = substTerm [ safe (var x []) _ ] t₂ --subst (λ x₁ → B.if ⌊ x₁ N.≟ 0 ⌋ then x else x₁ ∸ 1) t₂
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

ffi-lift1 : ∀ {n}
  → (fde : T n)
  → Term -- thing to wrap
  → Position -- seems to be only used to figure out in which directin to convert
  → List ℕ -- environment
  → Term
ffi-lift1 (set _) wr pos Γ = wr
ffi-lift1 (var k ∙ x) wr pos Γ = wr
ffi-lift1 (def nm ∙ x) wr pos Γ  = wr
ffi-lift1 {n} (π fde ∣ k ⇒ fde₁) wr pos Γ =
  lam visible (abs "x" bd)
  where ls = ffi-lift1 fde (var 0 []) (invertPosition pos) (shift 1 Γ)
        open import Reflection.DeBruijn
        toWrap = case k of
          λ { Keep → app (weaken 2 wr) (var 0 []) -- app (subst (N._+_ 2) wr) (var 0 [])
            ; Discard → weaken 2 wr -- subst (N._+_ 2) wr
            }
        rs = ffi-lift1 fde₁ toWrap pos (0 ∷ shift 2 Γ)
        bd = lett ls inn rs
ffi-lift1 (iso {l} x LOWₐ HIGHₐ) wr pos Γ =
  -- extract the conversion from the named iso
  -- apply unsafeConvert
  def (quote unsafeConvert)
    ( arg def-argInfo (tyFrom pos)
    ∷ arg def-argInfo (tyTo pos)
    ∷ arg def-argInfo conv
    ∷ arg def-argInfo (wr) ∷ [])
  where
        open import Reflection.Substitute
        ix = reverse $ downFrom (List.length Γ)
        s = {-substTerm (List.map (λ ix → safe (var ix []) _) Γ)-} subst (λ x → lookup' x Γ)
        
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

ffi-lift : (fde : T 0) → Term {- low term / function -} → Term
ffi-lift fde low  = ffi-lift1 fde low Pos []

open import Level


toIntPartIso : PartIso
  → Term
  → PartIsoInt
toIntPartIso p pₙ = record
  { wrappedₙ = pₙ
  }
-}
