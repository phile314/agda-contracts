module FFI.PartIso.Core where

open import Level as L
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat
open import Data.List as List

data Conversion {a b} (A : Set a) (B : Set b) : Set (L.suc (a L.⊔ b)) where
  total : (A → B) → Conversion A B
  withDec : (A → Dec B) → Conversion A B
  withMaybe : (A → Maybe B) → Conversion A B
  fail : Conversion A B

{-data ArgTys {c} : Set (L.suc c) where
  [] : ArgTys {c}
  _∷_ : (A : Set c) → ArgTys → ArgTys-}

ArgTys : ∀ {c} → Set (L.suc c)
ArgTys {c} = List (Set c)

data WithArgs {c} : (ArgTys {c}) → Set (L.suc c) where
  [] : WithArgs []
  _∷_ : {A : Set c} → (a : A) → {AS : ArgTys} → WithArgs AS → WithArgs (A List.∷ AS)

argsToTy : ∀ {b c} → ArgTys {c} → Set b → Set (b L.⊔ c)
argsToTy {b} {c} [] f = Lift {b} {c} f
argsToTy {b} {c} (x List.∷ a) f = x → argsToTy {b} {c} a f

open import Data.Product

record PartIso' {l} (agdaArgTys : ArgTys {l}) (HS : Set l) : Set (L.suc l) where
  field AGDA : Set l -- agda type
  field there : Conversion AGDA HS
  field back : Conversion HS AGDA

{-mkTy : ∀ {l} → (agdaArgTys : ArgTys {l}) (HS : Set l) (agdaArgs : WithArgs agdaArgTys) → Set (L.suc l)
mkTy = PartIso'-}
  
record PartIso {l} : Set (L.suc l) where
  field HSₐ : ArgTys {l}
  field AGDAₐ : ArgTys {l}
  field iso : argsToTy HSₐ (Σ (Set l) (λ hsty → (argsToTy AGDAₐ (PartIso' AGDAₐ hsty))))
  --WithArgs HSₐ → Σ (Set l) (λ hs → (WithArgs AGDAₐ → PartIso' AGDAₐ hs))

{-getFromType : ∀ {a b c argTys} → PartIso {c} {a} {b} argTys → WithArgs argTys → Set a
getFromType p args = PartIso'.FROM (PartIso.other p args)-}




open import Data.Fin
open import Reflection

data T {l} : ℕ → Set (L.suc l) where
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
    → PartIso {l}
    → List (T n) -- argument for HSₐ
    → List (T n) -- arguments for Agdaₐ
    → T n
  lift_ : ∀ {n k}
    → {p : k ≥″ n}
    → T n
    → T k

{-mkTy : ∀ {n} → T n → Set1
mkTy 
mkTy (v k ∙ x) = Set
mkTy (def x ∙ x₁) = Set
mkTy (π t ⇒ t₁) = mkTy t → mkTy t₁
mkTy (T.lift t) = mkTy t-}

def-argInfo : Arg-info
def-argInfo = arg-info visible relevant

{-# TERMINATING #-}
elArg : ∀ {n} → (t : T n) → Arg Term

-- getting Agda type
elAGDA : ∀ {n} → (t : T n) → Term
elAGDA (v k ∙ xs) = var (toℕ k) (List.map elArg xs)
elAGDA (def x ∙ xs) = def x (List.map elArg xs)
elAGDA (π t ⇒ t₁) = pi (arg def-argInfo (el unknown (elAGDA t))) (abs "" (el unknown (elAGDA t₁)))
elAGDA (T.lift t) = elAGDA t
elAGDA (set l) = sort (lit l)
elAGDA (iso i HSₐ AGDAₐ) = def (quote PartIso'.AGDA) [ arg def-argInfo {!!} ]

elArg t = arg def-argInfo (elAGDA t)

open import Data.Vec

vec⇔list : PartIso
vec⇔list = record
  { HSₐ = List.[ Set ]
  ; AGDAₐ = List.[ Lift ℕ ]
  ; iso = λ x → L.lift ((List (Lift x)) , (λ x₁ → L.lift (record { AGDA = Vec (Lift x) (lower x₁) })))
  }

fTy : T 0
fTy = π (set 0) ⇒ (π (def (quote ℕ) ∙ []) ⇒ (π (π (v (fromℕ 1) ∙ []) ⇒ (v (fromℕ 2) ∙ [])) ⇒ (π (iso vec⇔list List.[ v (fromℕ 2) ∙ [] ] List.[ T.lift (v (fromℕ 1) ∙ []) ]) ⇒ (iso vec⇔list List.[ (v (fromℕ 3) ∙ []) ] List.[ T.lift (v (fromℕ 2) ∙ [] )]))))

k : unquote (elAGDA fTy)
k = {!!}
