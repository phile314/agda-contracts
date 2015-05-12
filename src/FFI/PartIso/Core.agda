module FFI.PartIso.Core where

open import Level as L
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat
open import Data.List as List
open import Function

data Conversion {a b} (A : Set a) (B : Set b) : Set (L.suc (a L.⊔ b)) where
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

record PartIso' {l} (agdaArgTys : ArgTys) (HS : Set l) : Set (L.suc l) where
  field AGDA : Set l -- agda type
  field there : Conversion AGDA HS
  field back : Conversion HS AGDA

{-mkTy : ∀ {l} → (agdaArgTys : ArgTys {l}) (HS : Set l) (agdaArgs : WithArgs agdaArgTys) → Set (L.suc l)
mkTy = PartIso'-}
  
record PartIso : Set1 where
  field HSₐ : ArgTys
  field AGDAₐ : ArgTys
  field iso : argsToTy HSₐ (Σ (Set) (λ hsty → (argsToTy AGDAₐ (PartIso' AGDAₐ hsty))))
  --WithArgs HSₐ → Σ (Set l) (λ hs → (WithArgs AGDAₐ → PartIso' AGDAₐ hs))

{-getFromType : ∀ {a b c argTys} → PartIso {c} {a} {b} argTys → WithArgs argTys → Set a
getFromType p args = PartIso'.FROM (PartIso.other p args)-}




open import Data.Fin
open import Reflection

data T : ℕ → Set where
  set : (l : ℕ) → T 0
  -- var
  v_∙_ : ∀ {n}
    → (k : Fin n)
    → List (T n) -- arguments
    → T n
  -- term from outside
  def_∙_ : ∀ {n}
    → Name
    → List (T n)
    → T n
  π_⇒_ : ∀ {n}
    → T n -- type of the arg
    → T (ℕ.suc n) -- body
    → T n

  iso : ∀ {n}
    → Name --PartIso {l}
    → List (T n) -- argument for HSₐ
    → List (T n) -- arguments for Agdaₐ
    → T n
{-  lift_ : ∀ {n k}
    → {p : k ≥″ n}
    → T n
    → T k-}

{-mkTy : ∀ {n} → T n → Set1
mkTy 
mkTy (v k ∙ x) = Set
mkTy (def x ∙ x₁) = Set
mkTy (π t ⇒ t₁) = mkTy t → mkTy t₁
mkTy (T.lift t) = mkTy t-}

def-argInfo : Arg-info
def-argInfo = arg-info visible relevant

-- Part iso together with the name is has been unquoted into.
--PartIsoWithDecl : ∀ {l} → Set (L.suc l)
--PartIsoWithDecl = (PartIso × Name)

-- There is no way to apply a term to something, e.g.:
-- app (unquoteTerm (iso)) (args...)

-- apply
--applyHsArgs : ∀ {l} → PartIsoWithDecl {l} → Term
--applyHsArgs (proj₁ , proj₂) = def proj₂ {!!}

{-# TERMINATING #-}
elArg : ∀ {n} → (t : T n) → Arg Term

-- getting Agda type
elAGDA : ∀ {n} → (t : T n) → Term
elAGDA (v k ∙ xs) = var (toℕ k) (List.map elArg xs)
elAGDA (def x ∙ xs) = def x (List.map elArg xs)
elAGDA (π t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA t))) (abs "" (el unknown (elAGDA t₁)))
elAGDA (set l) = sort (lit l)
elAGDA (iso i HSₐ AGDAₐ) = def (quote PartIso'.AGDA) [ arg def-argInfo isoWithAgdaArgs ]
  where iso' = def (quote PartIso.iso) [ arg def-argInfo (def i []) ]
        isoWithHsArgs = def (quote proj₂) [ arg def-argInfo (app iso' (List.map (arg def-argInfo ∘ elAGDA) HSₐ)) ]
        isoWithAgdaArgs : Term
        isoWithAgdaArgs = app isoWithHsArgs (List.map (arg def-argInfo ∘ elAGDA) AGDAₐ)

elArg t = arg def-argInfo (elAGDA t)

open import Data.String

HsName : Set
HsName = String

data HS_Type : ℕ → Set where
  HS-var : ∀{n} (k : Fin n) → HS_Type n -- (k : Fin n)
  HS-App : ∀ {n} → (HS_Type n) → (HS_Type n) → (HS_Type n)
  -- shared rep.
  HS-Shared : ∀{n} → HsName → Name → HS_Type n
  HS-∀ : ∀ {n} → HS_Type (ℕ.suc n) → HS_Type n
  _HS⇒_ : ∀ {n} → HS_Type n → HS_Type n → HS_Type n

open import Data.Vec as Vec

{-HStoTy : ∀ {n} → HS_Type n → Term
HStoTy (HS-var x) = var (toℕ x) []
HStoTy (HS-App t t₁) = app (HStoTy t) List.[ arg def-argInfo (HStoTy t₁) ]
HStoTy (HS-Shared x x₁) = def x₁ []
HStoTy (HS-∀ t) = pi (arg def-argInfo (el {!!} {!!})) (abs "" (el {!!} {!HStoTy !}))
HStoTy (HS-⇒ t t₁) = {!!}-}

open import Data.String as S
open import Data.Nat.Show as NS

ΓP : ℕ → Set
ΓP n = Vec String n

printHSty1 : ∀ {n} → (env : ΓP n) → HS_Type n → String
printHSty1 e (HS-var k) = lookup k e
printHSty1 e (HS-App ty ty₁) = "(" S.++ printHSty1 e ty S.++ " " S.++ printHSty1 e ty₁ S.++ ")"
printHSty1 e (HS-Shared x x₁) = "(" S.++ x S.++ " as " S.++ showName x₁ S.++ ")"
printHSty1 {n} e (HS-∀ ty) = "(∀ " S.++ nm S.++ " . " S.++ printHSty1 e' ty S.++ ")"
  where nm = ("a" S.++ NS.show n)
        e' = nm Vec.∷ e
printHSty1 e (ty HS⇒ ty₁) = "(" S.++ printHSty1 e ty S.++ " → " S.++ printHSty1 e ty₁ S.++ ")"

printHSty : HS_Type 0 → String
printHSty = printHSty1 []

mapTy : HS_Type 0
mapTy = HS-∀ (((HS-var (fromℕ 0)) HS⇒ (HS-var (fromℕ 0))) HS⇒ ((HS-App listTy (HS-var (fromℕ 0))) HS⇒ HS-App listTy (HS-var (fromℕ 0))))
  where listTy = HS-Shared "HsList" (quote List)


-- off is the number of pis not introducting a forall
elHS1 : ∀ {n} (e : ℕ) → (t : T n) → Maybe (HS_Type (n ∸ e))
elHS1 e (set l) = nothing
elHS1 {n} e (v k ∙ x) with (toℕ k) ∸ e
... | p with (ℕ.suc p) ≤? n ∸ e
elHS1 e (v k ∙ x) | p | yes p₁ = just (HS-var ( fromℕ≤  p₁))
elHS1 e (v k ∙ x) | p | no ¬p = nothing
elHS1 e (def x ∙ x₁) = {!!}
elHS1 e (π set l ⇒ t₁) = just (HS-∀ {!!})
elHS1 e (π (iso x x1 x2) ⇒ t1) = {!!}
elHS1 e (π t ⇒ t₁) = {!!}
elHS1 e (iso x x₁ x₂) = {!!}

elHS : (t : T 0) → Maybe (HS_Type 0)
elHS t = elHS1 {0} 0 t

open import Data.Vec

{-vec⇔list : PartIso
vec⇔list = record
  { HSₐ = List.[ Set ]
  ; AGDAₐ = List.[ Lift ℕ ]
  ; iso = λ x → L.lift ((List (Lift x)) , (λ x₁ → L.lift (record { AGDA = Vec (Lift x) (lower x₁) })))
  }-}

open import Data.Integer as I

ℕ⇔ℤ : PartIso
ℕ⇔ℤ = record
  { HSₐ = []
  ; AGDAₐ = []
  ; iso = (ℤ , (record { AGDA = ℕ ; there = total (+_) ; back = withMaybe f }))
  }
  where f : ℤ → Maybe ℕ
        f -[1+ n ] = nothing
        f (+ n) = just n

gTy : T  0
gTy = π set 0 ⇒ (v (fromℕ 0) ∙ [])

--fTy : T 0
--fTy = π (set 0) ⇒ (π (def (quote ℕ) ∙ []) ⇒ (π (π (v (fromℕ 1) ∙ []) ⇒ (v (fromℕ 2) ∙ [])) ⇒ (π (iso vec⇔list List.[ v (fromℕ 2) ∙ [] ] List.[ T.lift (v (fromℕ 1) ∙ []) ]) ⇒ (iso vec⇔list List.[ (v (fromℕ 3) ∙ []) ] List.[ T.lift (v (fromℕ 2) ∙ [] )]))))

fTy2 : T 0
fTy2 = π (set 0) ⇒ (π (def (quote ℕ) ∙ []) ⇒ (π (π (v (fromℕ 1) ∙ []) ⇒ (v (fromℕ 2) ∙ [])) ⇒ (v (fromℕ 2) ∙ []))) -- ⇒ (π (iso vec⇔list List.[ v (fromℕ 2) ∙ [] ] List.[ T.lift (v (fromℕ 1) ∙ []) ]) ⇒ (iso vec⇔list List.[ (v (fromℕ 3) ∙ []) ] List.[ T.lift (v (fromℕ 2) ∙ [] )]))))

fTy3 : T 0
fTy3 = π (iso (quote ℕ⇔ℤ) [] []) ⇒ (iso (quote ℕ⇔ℤ) [] [])

fTy4 : T  0
fTy4 = iso (quote ℕ⇔ℤ) [] []

g : unquote (elAGDA gTy)
g = {!unquote (elAGDA fTy3)!}

--f : unquote (elAGDA fTy)
--f = {!!}
