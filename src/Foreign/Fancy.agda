module Foreign.Fancy where


open import Reflection

data PatLamNotAllowed : Set where

lamBody : Term → Term
lamBody (lam v (abs s x)) = lamBody x
lamBody (pat-lam cs args) = quoteTerm PatLamNotAllowed
lamBody (pi t₁ (abs s (el s₁ t))) = lamBody t
lamBody t = t

open import Foreign.Base
open import Foreign.Show
open import Level
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat as N
open import Data.List as List
open import Function



data Conversion {a b} (A : Set a) (B : Set b) : Set (Level.suc (a Level.⊔ b)) where
  total : (A → B) → Conversion A B
  withDec : (A → Dec B) → Conversion A B
  withMaybe : (A → Maybe B) → Conversion A B
  fail : Conversion A B

{-data ArgTys {c} : Set (L.suc c) where
  [] : ArgTys {c}
  _∷_ : (A : Set c) → ArgTys → ArgTys-}

ArgTys : ∀ {l} → Set (Level.suc l)
ArgTys {l} = List (Set l)

-- if we want dependent args, we could make WithArgs into a dependent list (chained Σ)
data WithArgs : (ArgTys ) → Set₁ where
  [] : WithArgs []
  _∷_ : {A : Set} → (a : A) → {AS : ArgTys} → WithArgs AS → WithArgs (A List.∷ AS)

argsToTy : ∀ {b} → ArgTys {b} → Set b → Set (b)
argsToTy {b} [] f = f
argsToTy {b} (x List.∷ a) f = x → argsToTy {b} a f

open import Data.Product

{-record PartIso' {l} (agdaArgTys : ArgTys) (HS : Set l) : Set (Level.suc l) where
  field AGDA : Set l -- agda type
  field there : Conversion AGDA HS
  field back : Conversion HS AGDA-}


open import Reflection

--withArgs : ∀ {b c} {C : Set c} {D : Set (L.suc b)} → (arg : ArgTys) → Set b → (argsToTy arg → C) → (C → D) → D
--withArgs = ?

Conversions : ∀ {l} → Set l → Set l → Set (Level.suc l)
Conversions HSₜ AGDAₜ = Conversion HSₜ AGDAₜ × Conversion AGDAₜ HSₜ

record PartIso' {l} (ALLₐ AGDAₐ : ArgTys) : Set (Level.suc l) where
  field HSₜ : Set l
        -- ... → (AgdaType, conversions)
        other : argsToTy AGDAₐ (Σ (Set l) (Conversions HSₜ))
        


record PartIso {l} : Set (Level.suc (Level.suc l)) where
  constructor mkPartIso
  field ALLₐ : ArgTys {Level.suc l}
        AGDAₐ : ArgTys {Level.suc l}
        iso : argsToTy ALLₐ (PartIso' {l} ALLₐ AGDAₐ)

record PartIsoInt {l} : Set (Level.suc (Level.suc l)) where
  field wrapped : PartIso {l}
--        wrappedₙ : Name
        HSₙ : Name -- the low agda ty; name of the agda rep of the HS data
        AGDAₙ : Name -- the high agda ty
--        foreign-data : Term
        foreign-data : Data.ForeignData HSₙ
        foreign-dataₜ : Term


open import Data.Fin
open import Reflection

data Discard : Set where
  discard : Discard
  pass : Discard

-- TODO discard only makes sense in positive (or negative??) positions, we should enforce that it is only specified there
data T {l} : ℕ → Set (Level.suc (Level.suc l)) where
  set : ∀ {n} → (l : ℕ) → T n -- this get erased at runtime anyway, so it doesn't matter what value of discard they get
  -- var
  v_∙_ : ∀ {n}
    → (k : Fin n)
    → List (T {l} n) -- arguments, we don't support keeping the arguments anyway, so just force discard here.
    → T n
  def_∙_ : ∀ {n}
    → (nm : Name)
    → {{ f : Data.ForeignData nm}}
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

open Foreign.Base.Fun

postulate
  error : {a : Set} → a
  notImpl : {a : Set} → a

{-# TERMINATING #-}
elArg : ∀ {l n} → (t : T {l} n) → Arg Term

-- getting Agda low type
elAGDA : ∀ {l n} (t : T {l} n) → Term
elAGDA (v k ∙ xs) = var (toℕ k) (List.map elArg xs)
elAGDA (def x ∙ xs) = def x (List.map elArg xs)
elAGDA (π  t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA t))) (abs "" (el unknown (elAGDA t₁)))
elAGDA (set l) = sort (lit l)
elAGDA (iso i HSₐ AGDAₐ) = def (PartIsoInt.HSₙ i) (List.map elArg HSₐ)

elArg {l} t = arg def-argInfo (elAGDA t)


getAgdaLowType : ∀ {l} → T {l} 0 → Term
getAgdaLowType = elAGDA

{-# TERMINATING #-}
elArg2 : ∀ {l n} → (t : T {l} n) → Arg Term

-- getting Agda low type
elAGDA2 : ∀ {l n} (t : T {l} n) → Term
elAGDA2 (v k ∙ xs) = var (toℕ k) (List.map elArg2 xs)
elAGDA2 (def x ∙ xs) = def x (List.map elArg2 xs)
elAGDA2 (π  t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA2 t))) (abs "" (el unknown (elAGDA2 t₁)))
elAGDA2 (set l) = sort (lit l)
elAGDA2 (iso i HSₐ AGDAₐ) = def (PartIsoInt.AGDAₙ i) (List.map elArg2 (HSₐ List.++ AGDAₐ))

elArg2 {l} t = arg def-argInfo (elAGDA2 t)

getAgdaHighType : ∀ {l} → T {l} 0 → Term
getAgdaHighType = elAGDA2


ffi_lift : ∀ {l} → (fde : T {l} 0) → Name {- name of the low level fun -} → Term
ffi_lift (set l₁) nm = ?
ffi_lift (v k ∙ x) nm = ?
ffi_lift (def nm ∙ x) nm₁ = ?
ffi_lift (π fde ⇒ fde₁) nm = ?
ffi_lift (iso x x₁ x₂) nm = ?


--postulate
  -- returns the Agda type before applying the isos
--  getAgdaLowType : ∀ {l} → T {l} 0 → Set l
  -- after the isos
--  getAgdaHighType : ∀ {l} → T {l} 0 → Term
  -- converting low iso to high iso
--  ffi_lift : ∀ {l} → (fde : T {l} 0) → Name {- name of the low level fun -} → Term --(unquote (getAgdaLowType {l} fde)) → (getAgdaHighType {l} fde)


open import Data.String
open import Level

{-
mapTy : ForeignSpec HS-UHC
mapTy = HS-UHC "Data.List.map" (∀' (((var 0) ⇒ (var 0)) ⇒ ((app listTy (var 0)) ⇒ app listTy (var 0))))
  where listTy : τ-Hs HS-UHC
        listTy = ty (quote List) (Data.HS-UHC "Data.List" (quote List) )
-}
open import Relation.Binary.PropositionalEquality

open import Category.Monad
open import Category.Monad.Indexed
open import Category.Applicative.Indexed

open Category.Monad.Indexed.RawIMonad {Level.zero} {Level.zero} Data.Maybe.monad

{-import Category.Monad
open Category.Monad.RawMonad {_} {Maybe}-}


open import Data.Nat.Properties.Simple

open import Data.List as L

--apps :

data SomethingBad : Set where

FAIL : Term
FAIL = def (quote SomethingBad) []

hsUhcWay : Arg Term
hsUhcWay = arg (arg-info hidden relevant) (con (quote FFIWay.HS-UHC) L.[] )

import Data.List.Base
-- off is the number of pis not introducting a forall
{-# TERMINATING #-}
getFFI1 : ∀ {l} → {n : ℕ} (e : ℕ) → (t : T {l} n) → Term
getFFI1 e (set l) = FAIL
getFFI1 e (v k ∙ x) = con (quote τ-Hs.var) ( hsUhcWay L.∷ L.[ arg def-argInfo (lit (nat (toℕ k))) ])
getFFI1 e (def x ∙ xs) =
  def (quote apps) (((arg def-argInfo (quoteTerm (ty {way = HS-UHC} x)))) L.∷ xs')
  where xs' = L.map (arg def-argInfo ∘ getFFI1 e) xs
getFFI1 {n} e (π (set l) ⇒ t₁) =
  con (quote ∀') L.[ arg def-argInfo (getFFI1 e t₁) ]
getFFI1 e (π t ⇒ t₁) =
  con (quote _⇒_) (arg def-argInfo (getFFI1 e t) L.∷ L.[ arg def-argInfo (getFFI1 (N.suc e) t₁) ])
-- problem:  Name is not a literal => we cannot unquote here.
-- solution 1: Return terms in elHS1, and unquote on top level.
getFFI1 e (iso x x₁ x₂) =
  def (quote apps)
    (hsUhcWay
    L.∷ arg def-argInfo  (con (quote ty) (arg def-argInfo (hsTy) L.∷ L.[ arg def-argInfo getForDat ] )) --L.∷ L.[ arg def-argInfo (PartIsoInt.foreign-dataₜ x)]))
    L.∷ (arg def-argInfo hsArgs)
    L.∷ L.[]
    )
  where hsTy = lit (name (PartIsoInt.HSₙ x))
        mkList : L.List Term → Term
        mkList (x L.∷ xs) = con (quote L._∷_) ((arg def-argInfo x) L.∷ L.[ arg def-argInfo (mkList xs) ])
        mkList [] = con (quote Data.List.Base.List.[]) []
        hsArgs = mkList (L.map (getFFI1 e) x₁)
        getForDat = def (quote Data.ForeignData.foreign-spec) L.[ arg def-argInfo (PartIsoInt.foreign-dataₜ x) ]

getFFI : ∀ {l} → (t : T {l} 0) → Term --(τ-Hs)
getFFI t = getFFI1 {_} {0} 0 t

open import Data.Vec hiding (_>>=_)



open import Data.Integer as I

postulate error2 : ∀ {a : Set} → a

postulate NoPI : Term

getOtherPI : Term → Term
getOtherPI (con c args) with Fun.lookup 3 args
getOtherPI (con c args) | just (arg _ t) = lamBody t
  where g : Term → Term
        g t  = t
getOtherPI (con c args) | _ = NoPI
getOtherPI t = NoPI

getHsTyNm : Term → Name
getHsTyNm t with getOtherPI t
... | ot = g ot
  where g : Term → Name
        g (con c₁ args₁) with Fun.lookup 3 args₁
        ... | just (arg _ (def nm _)) = nm
        ... | _ = error
        g _ = error2
{-getHsTyNm (con c args) | just (arg _ t) with lamBody t
... | (con c' args') with Fun.lookup 3 args'
... | _ | lk = {!!} --with Fun.lookup 3 args'
--... | lk2 = {!!}
... | _ = error-}
{-getHsTyNm (con c args) | just (arg i (con c' args')) with Fun.lookup 3 args'
getHsTyNm (con c args) | just (arg i₁ (con c' args')) | just (arg i (def nm _)) = nm
getHsTyNm (con c args) | just (arg i₁ (con c' args')) | just (arg i x) = error
getHsTyNm (con c args) | just (arg i (con c' args')) | nothing = error2-}
--getHsTyNm (con c args) | just _ = error2
--getHsTyNm (con c args) | _ = error2


getAgdaTyNm : Term → Name
getAgdaTyNm d with getOtherPI d
... | (con c args) = g args
  where h : Maybe (Arg Term) → Name
        h (just (arg _ (def nm _))) = nm
        h _ = error
        g : List (Arg Term) → Name
        g args with Fun.lookup 4 args
        g args₁ | just (arg _ k) with lamBody k
        ... | con _ args = h (Fun.lookup 4 args)
        ... | _ = error
        g args₁ | _ = error
... | k = error

toIntPartIso : ∀ {l} → PartIso {l} → (t : Term)
  → {{fd : Data.ForeignData (getHsTyNm t)}}
  → Term -- quoted fd
  → PartIsoInt
toIntPartIso p t {{fd}} fdₜ = record
  { HSₙ = getHsTyNm t
  ; AGDAₙ = getAgdaTyNm t
  ; wrapped = p
  ; foreign-data = fd
  ; foreign-dataₜ = fdₜ
  }

{-
instance
  blub : Data.ForeignData (quote L.List)
  blub = record { foreign-spec = Data.HS-UHC "Data.List.List" (quote L.List) }

HS-T : {l : Level} → Set (Level.suc (Level.suc Level.zero))
HS-T {l} = T {l} {pass} 0



list⇒vec : ∀ {l} {n : ℕ} {A : Set l} → List A → Maybe (Vec A n)
list⇒vec {_} {n} xs with n N.≟ L.length xs
list⇒vec xs | yes refl = just (Data.Vec.fromList xs)
list⇒vec xs | no ¬p = nothing

vec⇔list : (l : Level) → PartIsoInt {l}
vec⇔list l = toIntPartIso partIso (quoteTerm partIso) (quoteTerm blub)
  where
    partIso = mkPartIso L.[ Set l ] L.[ (Lift ℕ) ]
      (λ a → record
        { HSₜ = L.List a
        ; other = λ n → (Vec a (lower n)) , ( withMaybe list⇒vec , total Data.Vec.toList)})
        
--  { HSₐ = List.[ Set ]
--  ; AGDAₐ = List.[ Lift ℕ ]
--  ; iso = λ x → L.lift ((List (Lift x)) , (λ x₁ → L.lift (record { AGDA = Vec (Lift x) (lower x₁) })))
--  }

gTy : ∀ {l} → HS-T {l}
gTy = π pass - set 0 ⇒ (v pass - (fromℕ 0) ∙ [])

fTy : T 0
fTy =
  π pass - (set 0)
  ⇒ (π discard - (def↯ (quote ℕ) ∙ [])
  ⇒ (π pass - (π pass - (v pass - (fromℕ 1) ∙ [])
    ⇒ (v pass - (fromℕ 2) ∙ []))
  ⇒ (π pass - (iso (vec⇔list Level.zero) List.[ v pass - (fromℕ 2) ∙ [] ] List.[ {!!} ]) --(v ? - (fromℕ 1) ∙ []) ])
  ⇒ (iso (vec⇔list Level.zero) List.[ (v pass - (fromℕ 3) ∙ []) ] List.[ {!!} ])))) -- (v ? - (fromℕ 2) ∙ [] )]))))

--fTy2 : T 0
--fTy2 = π (set 0) ⇒ (π (def (quote ℕ) ∙ []) ⇒ (π (π (v (fromℕ 1) ∙ []) ⇒ (v (fromℕ 2) ∙ [])) ⇒ (v (fromℕ 2) ∙ []))) -- ⇒ (π (iso vec⇔list List.[ v (fromℕ 2) ∙ [] ] List.[ T.lift (v (fromℕ 1) ∙ []) ]) ⇒ (iso vec⇔list List.[ (v (fromℕ 3) ∙ []) ] List.[ T.lift (v (fromℕ 2) ∙ [] )]))))

fTy3 : HS-T
fTy3 = π pass - (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] [])

fTy4 : HS-T
fTy4 = iso ℕ⇔ℤ [] []

x : τ-Hs HS-UHC
x = {!show-τ-Hs {HS-UHC} L.[] (unquote (elHS fTy3))!} -- elHS gTy >>= (λ x₁ → {!unquote x!})
{-... | just x = {!x!} --elHS gTy
... | nothing = error-}

q : ∀ {a} → a
q = {!!}

record D : Set where
  constructor kk
  field k : ℕ

import Data.List

l : D
l = record { k = 2}

g : unquote (elAGDA gTy)
g = {!!}
--... | just x' = {!elHS gTy >>= show-τ-Hs Data.List.[]!}
--... | nothing = {!quoteTerm (ℕ⇔ℤ)!}

--q : PartIso
--q = unquote (quoteTerm ℕ⇔ℤ)


--f : unquote (elAGDA fTy)
--f = {!!}
-}
