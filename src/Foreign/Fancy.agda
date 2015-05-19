module Foreign.Fancy where

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

ArgTys : Set₁ --(L.suc c)
ArgTys = List (Set)

data WithArgs : (ArgTys ) → Set₁ where
  [] : WithArgs []
  _∷_ : {A : Set} → (a : A) → {AS : ArgTys} → WithArgs AS → WithArgs (A List.∷ AS)

argsToTy : ∀ {b} → ArgTys → Set b → Set (b)
argsToTy {b} [] f = f
argsToTy {b} (x List.∷ a) f = x → argsToTy {b} a f

open import Data.Product

record PartIso' {l} (agdaArgTys : ArgTys) (HS : Set l) : Set (Level.suc l) where
  field AGDA : Set l -- agda type
  field there : Conversion AGDA HS
  field back : Conversion HS AGDA

{-mkTy : ∀ {l} → (agdaArgTys : ArgTys {l}) (HS : Set l) (agdaArgs : WithArgs agdaArgTys) → Set (L.suc l)
mkTy = PartIso'-}

open import Reflection
record PartIso : Set1 where
  constructor mkPartIso
  field HSₐ : ArgTys
  field AGDAₐ : ArgTys
  field iso : argsToTy HSₐ (Σ (Set) (λ hsty → (argsToTy AGDAₐ (PartIso' AGDAₐ hsty))))
  --WithArgs HSₐ → Σ (Set l) (λ hs → (WithArgs AGDAₐ → PartIso' AGDAₐ hs))

{-getFromType : ∀ {a b c argTys} → PartIso {c} {a} {b} argTys → WithArgs argTys → Set a
getFromType p args = PartIso'.FROM (PartIso.other p args)-}

record PartIsoInt : Set1 where
  field wrapped : PartIso
  field HSₙ : Name
  field AGDAₙ : Name
  field foreign-data :  Data.ForeignData HS-UHC AGDAₙ




open import Data.Fin
open import Reflection

data T : ℕ → Set₂ where
  set : ∀ {n} → (l : ℕ) → T n
  -- var
  v_∙_ : ∀ {n}
    → (k : Fin n)
    → List (T n) -- arguments
    → T n
  -- term from outside
  def_∙_ : ∀ {n}
    → (nm : Name)
    → {{ f : Data.ForeignData HS-UHC nm}}
    → List (T n)
    → T n
  π_⇒_ : ∀ {n}
    → T n -- type of the arg
    → T (ℕ.suc n) -- body
    → T n

  iso : ∀ {n}
    → PartIsoInt
    → List (T n) -- argument for HSₐ
    → List (T n) -- arguments for Agdaₐ
    → T n

def-argInfo : Arg-info
def-argInfo = arg-info visible relevant

open Foreign.Base.Fun

{-# TERMINATING #-}
elArg : ∀ {n} → (t : T n) → Arg Term

-- getting Agda type
elAGDA : ∀ {n} → (t : T n) → Term
elAGDA (v k ∙ xs) = var (toℕ k) (List.map elArg xs)
elAGDA (def x ∙ xs) = def x (List.map elArg xs)
elAGDA (π t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA t))) (abs "" (el unknown (elAGDA t₁)))
elAGDA (set l) = sort (lit l)
elAGDA (iso i HSₐ AGDAₐ) = def (quote PartIso'.AGDA) [ arg def-argInfo isoWithAgdaArgs ]
  where iso' = def (quote PartIso.iso) [ arg def-argInfo (def {!!} []) ]
        isoWithHsArgs = def (quote proj₂) [ arg def-argInfo (app iso' (List.map (arg def-argInfo ∘ elAGDA) HSₐ)) ]
        isoWithAgdaArgs : Term
        isoWithAgdaArgs = app isoWithHsArgs (List.map (arg def-argInfo ∘ elAGDA) AGDAₐ)

elArg t = arg def-argInfo (elAGDA t)

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

-- off is the number of pis not introducting a forall
{-# TERMINATING #-}
elHS1 : {n : ℕ} (e : ℕ) → (t : T n) → Maybe Term --Maybe (τ-Hs {HS-UHC})
elHS1 e (set l) = nothing
elHS1 e (v k ∙ x) = just (def (quote τ-Hs.var) ((arg def-argInfo (def (quote FFIWay.HS-UHC) L.[])) L.∷ L.[ arg def-argInfo (lit (nat (toℕ k))) ]))
elHS1 e (def x ∙ xs) =
  mapM Data.Maybe.monad (elHS1 e) xs >>= λ xs' →
  return (def (quote apps) (((arg def-argInfo (quoteTerm (ty {way = HS-UHC} x)))) L.∷ {!xs'!}) ) --return (quoteTerm (apps (ty x) xs'))
elHS1 {n} e (π (set l) ⇒ t₁) =
  elHS1 e t₁ >>= λ t₁' →
  return (def (quote ∀') L.[ arg def-argInfo t₁' ])
elHS1 e (π t ⇒ t₁) =
  elHS1 e t >>= λ t' →
  elHS1 (ℕ.suc e) t₁ >>= λ t₁' →
  just (def (quote _⇒_) (arg def-argInfo t' L.∷ L.[ arg def-argInfo t₁' ]))
-- problem:  Name is not a literal => we cannot unquote here.
-- solution 1: Return terms in elHS1, and unquote on top level.
elHS1 e (iso x x₁ x₂) with mapM Data.Maybe.monad (elHS1 e) x₁
... | hsArgs = hsArgs >>= λ hsArgs' →
  return (def (quote ty) (arg def-argInfo (lit (name hsTy)) L.∷ {!!})) --just (apps (ty (unquote (def hsTy L.[ arg def-argInfo (def x []) ]))) hsArgs')
  where hsTy = PartIsoInt.HSₙ x --quote PartIso.HS
        isoT = L.[ arg def-argInfo (def {!!} []) ]

elHS : (t : T 0) → Maybe Term --(τ-Hs)
elHS t = elHS1 {0} 0 t

open import Data.Vec hiding (_>>=_)

{-vec⇔list : PartIso
vec⇔list = record
  { HSₐ = List.[ Set ]
  ; AGDAₐ = List.[ Lift ℕ ]
  ; iso = λ x → L.lift ((List (Lift x)) , (λ x₁ → L.lift (record { AGDA = Vec (Lift x) (lower x₁) })))
  }-}

open import Data.Integer as I

postulate error : ∀ {a} → a
          error2 : ∀ {a} → a

getHsTyNm : Term → Name
getHsTyNm (con c args) with Fun.lookup 2 args
getHsTyNm (con c args) | just (arg i (con c' args')) with Fun.lookup 4 args'
getHsTyNm (con c args) | just (arg i₁ (con c' args')) | just (arg i (def nm _)) = nm
getHsTyNm (con c args) | just (arg i₁ (con c' args')) | just (arg i x) = error
getHsTyNm (con c args) | just (arg i (con c' args')) | nothing = error2
getHsTyNm (con c args) | just _ = error2
getHsTyNm (con c args) | nothing = error2
getHsTyNm d = error

toIntPartIso : PartIso → (t : Term) → {{fd : Data.ForeignData HS-UHC (getHsTyNm t)}} → PartIsoInt
toIntPartIso p t {{fd}} = record
  { HSₙ = getHsTyNm t
  ; wrapped = p
  ; foreign-data = fd
  }

instance
  bla : Data.ForeignData HS-UHC (quote ℤ)
  bla = record { foreign-spec = Data.HS-UHC "Integer" }

ℕ⇔ℤ : PartIsoInt
ℕ⇔ℤ = toIntPartIso partIso (quoteTerm partIso)
  where f : ℤ → Maybe ℕ
        f -[1+ n ] = nothing
        f (+ n) = just n
        partIso = mkPartIso [] [] (ℤ , (record { AGDA = ℕ ; there = total (+_) ; back = withMaybe f }))

gTy : T  0
gTy = π set 0 ⇒ (v (fromℕ 0) ∙ [])

--fTy : T 0
--fTy = π (set 0) ⇒ (π (def (quote ℕ) ∙ []) ⇒ (π (π (v (fromℕ 1) ∙ []) ⇒ (v (fromℕ 2) ∙ [])) ⇒ (π (iso vec⇔list List.[ v (fromℕ 2) ∙ [] ] List.[ T.lift (v (fromℕ 1) ∙ []) ]) ⇒ (iso vec⇔list List.[ (v (fromℕ 3) ∙ []) ] List.[ T.lift (v (fromℕ 2) ∙ [] )]))))

--fTy2 : T 0
--fTy2 = π (set 0) ⇒ (π (def (quote ℕ) ∙ []) ⇒ (π (π (v (fromℕ 1) ∙ []) ⇒ (v (fromℕ 2) ∙ [])) ⇒ (v (fromℕ 2) ∙ []))) -- ⇒ (π (iso vec⇔list List.[ v (fromℕ 2) ∙ [] ] List.[ T.lift (v (fromℕ 1) ∙ []) ]) ⇒ (iso vec⇔list List.[ (v (fromℕ 3) ∙ []) ] List.[ T.lift (v (fromℕ 2) ∙ [] )]))))

fTy3 : T 0
fTy3 = π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] [])

fTy4 : T  0
fTy4 = iso ℕ⇔ℤ [] []

x : Maybe (τ-Hs)
x = {!!} --elHS gTy

record D : Set where
  constructor kk
  field k : ℕ

import Data.List

l : D
l = record { k = 2}

g : unquote (elAGDA gTy)
g with x
... | just x' = {!elHS gTy >>= show-τ-Hs Data.List.[]!}
... | nothing = {!quoteTerm (ℕ⇔ℤ)!}

--q : PartIso
--q = unquote (quoteTerm ℕ⇔ℤ)


--f : unquote (elAGDA fTy)
--f = {!!}
