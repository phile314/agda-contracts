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


open import Reflection

data PatLamNotAllowed : Set where

lamBody : Term → Term
lamBody (lam v (abs s x)) = lamBody x
lamBody (pat-lam cs args) = quoteTerm PatLamNotAllowed
lamBody (pi t₁ (abs s (el s₁ t))) = lamBody t
lamBody t = t

open import Level
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat as N
--open import Data.List as List
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

{-
record PartIso' {l} (LOWₐ HIGHₐ : ArgTys) : Set (Level.suc l) where
  field HSₜ : Set l
        -- ... → (AgdaType, conversions)
        other : argsToTy HIGHₐ (Σ (Set l) (Conversions HSₜ))
-}
record PartIso {l} : Set (Level.suc (Level.suc l)) where
  constructor mkPartIso
  field LOWₐ : ArgTys {Level.suc l} -- this are the common arguments
        HIGHₐ : ArgTys {Level.suc l} -- agda only arguments
--        iso : argsToTy LOWₐ (PartIso' {l} LOWₐ HIGHₐ)
        iso : argsToTy LOWₐ (Σ (Set l) (λ HSₜ →
                       argsToTy HIGHₐ (Σ (Set l) (Conversions HSₜ))))

record PartIsoInt {l} : Set (Level.suc (Level.suc l)) where
  field wrapped : PartIso {l}
        wrappedₙ : Name -- name of the part iso
        HSₙ : Name -- the low agda ty; name of the agda rep of the HS data
        AGDAₙ : Name -- the high agda ty

applyArgs : ∀ {l} → {aTys : ArgTys {l}} {A : Set l} → (f : argsToTy aTys A) → WithArgs aTys → A
applyArgs {aTys = []} f [] = f
applyArgs {aTys = A₁ ∷ aTys} f (a , args) = applyArgs (f a) args


open import Data.Fin
open import Reflection

data Discard : Set where
  discard : Discard
  pass : Discard

data Position : Set where
  Pos : Position
  Neg : Position

invertPosition : Position → Position
invertPosition Pos = Neg
invertPosition Neg = Pos

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
    → PartIsoInt {l}
    → List (T {l} n) -- argument for HSₐ
    → List (T {l} n) -- arguments for Agdaₐ
    → T n


def-argInfo : Arg-info
def-argInfo = arg-info visible relevant

--open Foreign.Base.Fun

postulate
  error : {a : Set} → a
  error2 : {a : Set} → a
  notImpl : {a : Set} → a

{-# TERMINATING #-}
elArg : ∀ {l n} → (t : T {l} n) → Arg Term

-- getting Agda low type
elAGDA : ∀ {l n} (t : T {l} n) → Term
elAGDA (var k ∙ xs) = var (toℕ k) (List.map elArg xs)
elAGDA (def x ∙ xs) = def x (List.map elArg xs)
elAGDA (π  t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA t))) (abs "" (el unknown (elAGDA t₁)))
elAGDA (set l) = sort (lit l)
elAGDA (iso i HSₐ AGDAₐ) = def (PartIsoInt.HSₙ i) (List.map elArg HSₐ)

elArg {l} t = arg def-argInfo (elAGDA t)


getAgdaLowType : ∀ {l} → T {l} 0 → Term
getAgdaLowType = elAGDA

{-# TERMINATING #-}
elArg2 : ∀ {l n} → (t : T {l} n) → Arg Term

-- getting Agda high type
elAGDA2 : ∀ {l n} (t : T {l} n) → Term
elAGDA2 (var k ∙ xs) = var (toℕ k) (List.map elArg2 xs)
elAGDA2 (def x ∙ xs) = def x (List.map elArg2 xs)
elAGDA2 (π  t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA2 t))) (abs "" (el unknown (elAGDA2 t₁)))
elAGDA2 (set l) = sort (lit l)
elAGDA2 (iso i HSₐ AGDAₐ) = def (PartIsoInt.AGDAₙ i) (List.map elArg2 (HSₐ List.++ AGDAₐ))

elArg2 {l} t = arg def-argInfo (elAGDA2 t)

getAgdaHighType : ∀ {l} → T {l} 0 → Term
getAgdaHighType = elAGDA2

mkAbs : (n : ℕ) → Term → Term
mkAbs ℕ.zero body = body
mkAbs (ℕ.suc n) body = lam visible (abs "" (mkAbs n body))

shift : ℕ → List ℕ → List ℕ
shift k = List.map (N._+_ k)

lett_inn_ : Term → Term → Term
lett_inn_ t₁ t₂ = app (lam visible (abs "" t₂)) [ arg (arg-info visible relevant) t₁ ]

open import Data.String
postulate
  conversionFailure : ∀ {a} → {A : Set a} → String → A

unsafeConvert : ∀ {a b} {A : Set a} {B : Set b} → Conversion A B → A → B
unsafeConvert (total x) x₁ = x x₁
unsafeConvert (withDec x) x₁ with x x₁
unsafeConvert (withDec x) x₁ | yes p = p
unsafeConvert (withDec x) x₁ | no ¬p = conversionFailure ""
unsafeConvert (withMaybe x) x₁ with x x₁
unsafeConvert (withMaybe x) x₁ | just x₂ = x₂
unsafeConvert (withMaybe x) x₁ | nothing = conversionFailure ""
unsafeConvert fail x = conversionFailure ""

last : {A : Set} → List A → A
last [] = error
last (x ∷ []) = x
last (x ∷ xs) = last xs

mkArg : ℕ → Arg Term
mkArg i = arg (arg-info visible relevant) (var i [])

postulate error5 : Term

{-# TERMINATING #-}
substTerm : ∀ {l n} → List ℕ → (fde : T {l} n)  → Term
substTerm Γ (set l₁) = notImpl
substTerm Γ (var k ∙ x) with lookup (toℕ k) Γ
substTerm Γ (var k ∙ x₁) | just x = var x (List.map (arg def-argInfo ∘ substTerm Γ) x₁)
substTerm Γ (var k ∙ x) | nothing = error5
substTerm Γ (def nm ∙ x) = def nm (List.map (arg def-argInfo ∘ substTerm Γ) x)
substTerm Γ (π fde ⇒ fde₁) = error
substTerm Γ (iso x HSₐ AGDAₐ) = error

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
  def (quote unsafeConvert) (lvl ∷ lvl ∷ tyFrom pos ∷ tyTo pos ∷ getConv2 pos ∷ arg def-argInfo (wr Γ) ∷ [])
  where lvl : Arg Term
        lvl = arg (arg-info hidden relevant) (quoteTerm Level.zero) -- TODO here we have to insert the proper level, not just 0....
        mkLift : Term → Term
        mkLift t = con (quote Level.lift) [ arg def-argInfo t ]
        iso' : Term
        iso' = app (def (quote PartIso.iso) [ arg def-argInfo (def (PartIsoInt.wrappedₙ x) []) ])
          (List.map (arg def-argInfo ∘ mkLift ∘ substTerm Γ) (LOWₐ))
        other' : Term
        other' = app ( def (quote proj₂) [ arg def-argInfo iso' ] )
          (List.map (arg def-argInfo ∘ mkLift ∘ substTerm Γ) (HIGHₐ))
        p2 : Term
        p2 = def (quote proj₂) [ arg def-argInfo other' ]
        getConv : Position → Term
        getConv Pos = (def (quote proj₁) [ arg def-argInfo p2 ]) 
        getConv Neg = (def (quote proj₂) [ arg def-argInfo p2 ])
{-        allArgs = LOWₐ List.++ HIGHₐ
        trArgs : List Term
        trArgs = List.map (mkLift ∘ substTerm Γ) allArgs-}
        getConv2 : Position → Arg Term
        getConv2 pos = arg def-argInfo (app (getConv pos) []) -- (List.map (arg def-argInfo) trArgs))
        tyAgda : Term
        tyAgda = def (PartIsoInt.AGDAₙ x) (List.map (arg def-argInfo ∘ substTerm Γ) (LOWₐ List.++ HIGHₐ))
        tyHs : Term
        tyHs = def (PartIsoInt.HSₙ x) (List.map (arg def-argInfo ∘ substTerm Γ) LOWₐ)
        tyFrom : Position → Arg Term
        tyFrom Pos = arg (arg-info hidden relevant) tyHs
        tyFrom Neg = arg (arg-info hidden relevant) tyAgda
        tyTo : Position → Arg Term
        tyTo Pos = arg (arg-info hidden relevant) tyAgda
        tyTo Neg = arg (arg-info hidden relevant) tyHs
--ffi-lift1 (iso x _ _) _ _ _ = notImpl

ffi-lift : ∀ {l} → (fde : T {l} 0) → Name {- name of the low level fun -} → Term
ffi-lift fde nm  = ffi-lift1 fde (λ Γ → def nm (List.map mkArg (List.reverse Γ))) Pos []

open import Level
open import Data.List as L

data SomethingBad : Set where

FAIL : Term
FAIL = def (quote SomethingBad) []


postulate NoPI : Term

getOtherPI : Term → Term
getOtherPI (con c args) with lookup 3 args
getOtherPI (con c args) | just (arg _ t) = lamBody t
  where g : Term → Term
        g t  = t
getOtherPI (con c args) | _ = NoPI
getOtherPI t = NoPI

getHsTyNm : Term → Name
getHsTyNm t with getOtherPI t
... | ot = g ot
  where g : Term → Name
        g (con c₁ args₁) with lookup 3 args₁
        ... | just (arg _ (def nm _)) = nm
        ... | _ = error
        g _ = error2

getAgdaTyNm : Term → Name
getAgdaTyNm d with getOtherPI d
... | (con c args) = g args
  where h : Maybe (Arg Term) → Name
        h (just (arg _ (def nm _))) = nm
        h _ = error
        g : List (Arg Term) → Name
        g args with lookup 4 args
        g args₁ | just (arg _ k) with lamBody k
        ... | con _ args = h (lookup 4 args)
        ... | _ = error
        g args₁ | _ = error
... | k = error

toIntPartIso : ∀ {l}
  → PartIso {l}
  → Name --part iso name
  → (t : Term) -- quoted part iso
  → PartIsoInt
toIntPartIso p pₙ pₜ = record
  { HSₙ = getHsTyNm pₜ
  ; AGDAₙ = getAgdaTyNm pₜ
  ; wrapped = p
  ; wrappedₙ = pₙ
  }
