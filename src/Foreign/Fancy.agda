module Foreign.Fancy where


open import Reflection

data PatLamNotAllowed : Set where

lamBody : Term → Term
lamBody (lam v (abs s x)) = lamBody x
lamBody (pat-lam cs args) = quoteTerm PatLamNotAllowed
lamBody (pi t₁ (abs s (el s₁ t))) = lamBody t
lamBody t = t

open import Foreign.Base
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
        HSₙ : Name
        AGDAₙ : Name
--        foreign-data : Term
        foreign-data : Data.ForeignData HS-UHC AGDAₙ
        foreign-dataₜ : Term


open import Data.Fin
open import Reflection

data Discard : Set where
  discard : Discard
  pass : Discard

-- TODO discard only makes sense in positive (or negative??) positions, we should enforce that it is only specified there
data T {l} : {d : Discard} → ℕ → Set₂ where
  set : ∀ {n} → {d : Discard} → (l : ℕ) → T {_} {d} n -- this get erased at runtime anyway, so it doesn't matter what value of discard they get
  -- var
  v_-_∙_ : ∀ {n}
    → (d : Discard) -- we don't enforce in the AST that the thing we pass on can actually be passed on. Should always be "discard" if args is not empty
    → (k : Fin n)
    → List (T {l} {d} n) -- arguments, we don't support keeping the arguments anyway, so just force discard here.
    → T {_} {d} n
  -- term from outside, getting discarded
  def↯_∙_ : ∀ {n}
    → (nm : Name)
    → List (T {l} {discard} n)
    → T {_} {discard} n
  -- term from outside, getting passed to hs
  def⇓_∙_ : ∀ {n}
    → (nm : Name)
    → {{ f : Data.ForeignData HS-UHC nm}}
    → List (T {l} {pass} n)
    → T {_} {pass} n
  π_-_⇒_ : ∀ {n D} -- D = if the whole things gets discarded
    → (d : Discard) -- if the arguments gets passed to the body
    → T {l} {d} n -- type of the arg
    → T {l} {D} (ℕ.suc n) -- body
    → T {_} {D} n

  iso : ∀ {n}
    → PartIsoInt {l}
    → List (T {l} {pass} n) -- argument for HSₐ
    → List (T {l} {discard} n) -- arguments for Agdaₐ
    → T {_} {pass} n

  ⇓-to-↯_ : ∀ {n}
    → T {l} {pass} n
    → T {l} {discard} n

def-argInfo : Arg-info
def-argInfo = arg-info visible relevant

open Foreign.Base.Fun

{-# TERMINATING #-}
elArg : ∀ {d l n} → (t : T {l} {d} n) → Arg Term

-- getting Agda type
elAGDA : ∀ {d l n} → (t : T {l} {d}  n) → Term
elAGDA (v d - k ∙ xs) = var (toℕ k) (List.map elArg xs)
elAGDA (def↯ x ∙ xs) = {!!}
elAGDA (def⇓ x ∙ xs) = def x (List.map elArg xs)
elAGDA (π d - t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA t))) (abs "" (el unknown (elAGDA t₁)))
elAGDA (set l) = sort (lit l)
elAGDA (iso i HSₐ AGDAₐ) = unquote-term {!!} {!!}
  where wr = PartIsoInt.wrapped i
elAGDA (⇓-to-↯ t) = {!!}

{-def (quote PartIso'.AGDA) [ arg def-argInfo isoWithAgdaArgs ]
  where iso' = def (quote PartIso.iso) [ arg def-argInfo (def (PartIsoInt.AGDAₙ i) []) ]
        isoWithHsArgs = def (quote proj₂) [ arg def-argInfo (app iso' (List.map (arg def-argInfo ∘ elAGDA) HSₐ)) ]
        isoWithAgdaArgs : Term
        isoWithAgdaArgs = app isoWithHsArgs (List.map (arg def-argInfo ∘ elAGDA) AGDAₐ)-}

elArg {l} t = arg def-argInfo (elAGDA t)

open import Data.String
open import Level

mapTy : ForeignSpec HS-UHC
mapTy = HS-UHC "Data.List.map" (∀' (((var 0) ⇒ (var 0)) ⇒ ((app listTy (var 0)) ⇒ app listTy (var 0))))
  where listTy : τ-Hs
        listTy = ty (quote List) {{record { foreign-spec = Data.HS-UHC "Data.List" }}}

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

import Data.List.Base
-- off is the number of pis not introducting a forall
{-# TERMINATING #-}
elHS1 : ∀ {d l} → {n : ℕ} (e : ℕ) → (t : T {l} {d} n) → Term
elHS1 e (set l) = FAIL
elHS1 e (v d - k ∙ x) = con (quote τ-Hs.var) ( L.[ arg def-argInfo (lit (nat (toℕ k))) ])
elHS1 e (def↯ x ∙ xs) = {!!}
elHS1 e (def⇓ x ∙ xs) =
  def (quote apps) (((arg def-argInfo (quoteTerm (ty {way = HS-UHC} x)))) L.∷ xs')
  where xs' = L.map (arg def-argInfo ∘ elHS1 e) xs
elHS1 {n} e (π d - (set l) ⇒ t₁) =
  con (quote ∀') L.[ arg def-argInfo (elHS1 e t₁) ]
elHS1 e (π d - t ⇒ t₁) =
  con (quote _⇒_) (arg def-argInfo (elHS1 e t) L.∷ L.[ arg def-argInfo (elHS1 (N.suc e) t₁) ])
-- problem:  Name is not a literal => we cannot unquote here.
-- solution 1: Return terms in elHS1, and unquote on top level.
elHS1 e (iso x x₁ x₂) =
  def (quote apps)
    ( arg def-argInfo  (con (quote ty) (arg def-argInfo (hsTy) L.∷ L.[] )) --L.∷ L.[ arg def-argInfo (PartIsoInt.foreign-dataₜ x)]))
    L.∷ (arg def-argInfo hsArgs)
    L.∷ L.[]
    )
  where hsTy = lit (name (PartIsoInt.HSₙ x))
        mkList : L.List Term → Term
        mkList (x L.∷ xs) = con (quote L._∷_) ((arg def-argInfo x) L.∷ L.[ arg def-argInfo (mkList xs) ])
        mkList [] = con (quote Data.List.Base.List.[]) []
        hsArgs = mkList (L.map (elHS1 e) x₁)
elHS1 e (⇓-to-↯ t) = {!!}

elHS : ∀ {l} → (t : T {l} {pass} 0) → Term --(τ-Hs)
elHS t = elHS1 {pass} {_} {0} 0 t

open import Data.Vec hiding (_>>=_)



open import Data.Integer as I

postulate error : ∀ {a} → a
          error2 : ∀ {a} → a


getHsTyNm : Term → Name
getHsTyNm (con c args) with Fun.lookup 3 args
getHsTyNm (con c args) | just (arg _ t) = g (lamBody t)
  where g : Term → Name
        g (con c₁ args₁) with Fun.lookup 3 args₁
        ... | just (arg _ (def nm _)) = nm
        ... | _ = error
        g _ = error2
getHsTyNm (con c args) | _ = error
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
getHsTyNm d = error

getForeignData : Term → Name
getForeignData (con c args) with Fun.lookup 2 args
... | l = {!!}
getForeignData d = error

toIntPartIso : ∀ {l} → PartIso {l} → (t : Term)
  → {{fd : Data.ForeignData HS-UHC (getHsTyNm t)}}
  → Term -- quoted fd
  → PartIsoInt
toIntPartIso p t {{fd}} fdₜ = record
  { HSₙ = getHsTyNm t
  ; AGDAₙ = {!!}
  ; wrapped = p
  ; foreign-data = fd
  ; foreign-dataₜ = fdₜ
  }

instance
  bla : Data.ForeignData HS-UHC (quote ℤ)
  bla = record { foreign-spec = Data.HS-UHC "Integer" }
  blub : Data.ForeignData HS-UHC (quote L.List)
  blub = record { foreign-spec = Data.HS-UHC "Data.List.List" }

HS-T : {l : Level} → Set (Level.suc (Level.suc Level.zero))
HS-T {l} = T {l} {pass} 0

ℕ⇔ℤ : PartIsoInt
ℕ⇔ℤ = toIntPartIso partIso (quoteTerm partIso) (quoteTerm bla)
  where f : ℤ → Maybe ℕ
        f -[1+ n ] = nothing
        f (+ n) = just n
        partIso : PartIso
        partIso = mkPartIso [] [] (record { HSₜ = ℤ ; other = ℕ , ((withMaybe f) , (total (+_))) })

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

x : τ-Hs {HS-UHC}
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
