module Foreign.Fancy where

open import Foreign.Base
open import Level as L
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat as N
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
  where iso' = def (quote PartIso.iso) [ arg def-argInfo (def i []) ]
        isoWithHsArgs = def (quote proj₂) [ arg def-argInfo (app iso' (List.map (arg def-argInfo ∘ elAGDA) HSₐ)) ]
        isoWithAgdaArgs : Term
        isoWithAgdaArgs = app isoWithHsArgs (List.map (arg def-argInfo ∘ elAGDA) AGDAₐ)

elArg t = arg def-argInfo (elAGDA t)

open import Data.String
open import Level

mapTy : ForeignSpec HS-UHC
mapTy = HS-UHC "Data.List.map" (∀' (((var (fromℕ 0)) ⇒ (var (fromℕ 0))) ⇒ ((app listTy (var (fromℕ 0))) ⇒ app listTy (var (fromℕ 0)))))
  where listTy : τ-Hs 1
        listTy = ty (quote List) {{record { foreign-spec = Data.HS-UHC "Data.List" }}}

open import Relation.Binary.PropositionalEquality

open import Category.Monad
open import Category.Monad.Indexed
open import Category.Applicative.Indexed

open Category.Monad.Indexed.RawIMonad {L.zero} {L.zero} Data.Maybe.monad

{-import Category.Monad
open Category.Monad.RawMonad {_} {Maybe}-}



open import Data.Nat.Properties.Simple

{-
Goal: Maybe (τ-Hs (toℕ (n ℕ- e)))
————————————————————————————————————————————————————————————
t' : Maybe (τ-Hs (toℕ (n N.+ 1 ℕ- inject+ 1 e)))
t₁ : T (ℕ.suc n)
l  : ℕ
e  : Fin (ℕ.suc n)
n  : ℕ
-}

open Relation.Binary.PropositionalEquality.≡-Reasoning
--lem1 : ∀ {n} {e : Fin (ℕ.suc n)} → ((n N.+ 1) ℕ- (inject+ 1 e)) ≡ (Fin.suc (n ℕ- e))
--lem1 = ?

module A where
  open import Relation.Binary.HeterogeneousEquality as H
  lem3 : ∀ {n : ℕ} {e : Fin (ℕ.suc n)} → ((n N.+ 1) ℕ- (inject+ 1 e)) ≅ (Fin.suc (n ℕ- e))
  lem3 {ℕ.zero} {Fin.zero} = refl
  lem3 {ℕ.zero} {Fin.suc ()}
  lem3 {ℕ.suc n} {Fin.zero} rewrite +-comm n 1 = refl
  lem3 {ℕ.suc n} {Fin.suc e} = lem3 {n} {e}
--  ... | p = p 

open A
open import Relation.Binary.HeterogeneousEquality as H using ()

lem4 : ∀ {n} {k : Fin n} → ℕ.suc (toℕ k) ≡ toℕ (Fin.suc k)
lem4 = refl

lem6 : ∀ {n} {e : Fin n} → toℕ (inject₁ e) ≡ toℕ e
lem6 {e = Fin.zero} = refl
lem6 {e = Fin.suc e} = cong ℕ.suc lem6


≡-to-≤ : {a b : ℕ} → a ≡ b → a N.≤ b
≡-to-≤ {ℕ.zero} refl = z≤n
≡-to-≤ {ℕ.suc a} refl = s≤s (≡-to-≤ refl)

lem10 : ∀ {n} {e : Fin (ℕ.suc n)} → (toℕ e) N.≤ n
lem10 {ℕ.zero} {Fin.zero} = z≤n
lem10 {ℕ.zero} {Fin.suc ()}
lem10 {ℕ.suc n} {Fin.zero} = z≤n
lem10 {ℕ.suc n} {Fin.suc e} = s≤s lem10

open import Data.Nat.Properties

lem9 : ∀ {n} {e : Fin (ℕ.suc n)} → 2 N.+ n ∸ (toℕ (inject₁ e)) ≡ 1 N.+ (1 N.+ n ∸ toℕ e)
lem9 {n} {e} = begin
    2 N.+ n ∸ toℕ (inject₁ e)
  ≡⟨ cong (λ x → 2 N.+ n ∸ x) (lem6 {_} {e} )⟩
    ((1 N.+ 1) N.+ n) ∸ toℕ e
  ≡⟨ +-∸-assoc (1 N.+ 1) {n} {toℕ e} lem10 ⟩
    1 N.+ (1 N.+ (n ∸ toℕ e))
  ≡⟨ cong (λ x → 1 N.+ x) (sym (+-∸-assoc 1 {n} {toℕ e} lem10)) ⟩
    1 N.+ ((1 N.+ n) ∸ toℕ e)
  ∎

--  ℕ.suc (ℕ.suc n) ∸ toℕ (inject₁ e) N.≤ ℕ.suc (ℕ.suc n ∸ toℕ e)

--  Fin.suc (n ℕ- e) ≡  inject≤ ((ℕ.suc n) ℕ- (inject₁ e)) ...
-- Goal: ℕ.suc (ℕ.suc n) ∸ toℕ (inject₁ e) ≡ ℕ.suc (ℕ.suc n ∸ toℕ e)
lem5 : ∀ {n} {e : Fin (ℕ.suc n)} → Fin.suc (n ℕ- e) ≡ inject≤ {_} {ℕ.suc (ℕ.suc n ∸ toℕ e)} ((ℕ.suc n) ℕ- (inject₁ e))(≡-to-≤ {ℕ.suc (ℕ.suc n) ∸ toℕ (inject₁ e)} {ℕ.suc (ℕ.suc n ∸ toℕ e)} (lem9 {n} {e}))
lem5 {e = Fin.zero} = {!!}
lem5 {e = Fin.suc e} = {!!}
{-lem5 {n} {e} = begin
    Fin.suc (n ℕ- e)
  ≡⟨ {!!} ⟩
    {!!}
  ≡⟨ {!!} ⟩
    inject≤ {_} {ℕ.suc (ℕ.suc n ∸ toℕ e)} ((ℕ.suc n) ℕ- (inject₁ e))(≡-to-≤ {ℕ.suc (ℕ.suc n) ∸ toℕ (inject₁ e)} {ℕ.suc (ℕ.suc n ∸ toℕ e)} (lem9 {n} {e}))
    ∎-}

open import Data.Fin.Properties

lem : {n : ℕ} {e : Fin (ℕ.suc n)} → (ℕ.suc (toℕ (n ℕ- e))) ≡ toℕ ((ℕ.suc n) ℕ- (inject₁ e))
lem {n} {e} = begin
    (ℕ.suc (toℕ (n ℕ- e)))
  ≡⟨ lem4 ⟩
    toℕ (Fin.suc (n ℕ- e))
  ≡⟨ cong toℕ (lem5 {n} {e}) ⟩
    toℕ (inject≤ {_} { ℕ.suc (ℕ.suc n ∸ toℕ e)} (ℕ.suc n ℕ- inject₁ e) (≡-to-≤ { ℕ.suc (ℕ.suc n) ∸ toℕ (inject₁ e)} {ℕ.suc (ℕ.suc n ∸ toℕ e)} (lem9 {n} {e})))
  ≡⟨ inject≤-lemma (ℕ.suc n ℕ- inject₁ e) (≡-to-≤ (lem9 {n} {e})) ⟩
    toℕ ((ℕ.suc n) ℕ- (inject₁ e))
  ∎

{-lem {ℕ.zero} {Fin.zero} = refl
lem {ℕ.zero} {Fin.suc ()}
lem {ℕ.suc n} {e} = {!!}-}

lem2 : ∀ {n} → (n N.+ 1) ≡ ℕ.suc n
lem2 {ℕ.zero} = refl
lem2 {ℕ.suc n} = cong ℕ.suc lem2

k : ∀ {n} → T (ℕ.suc n) → T (n N.+ 1)
k {n} t rewrite lem2 {n} = t

m : ∀ {n} {e : Fin (ℕ.suc n)} {w : FFIWay} → τ-Hs {w} (toℕ (ℕ.suc n ℕ- inject₁ e)) → τ-Hs {w} (ℕ.suc (toℕ (n ℕ- e)))
m {n} {e}  t rewrite lem {n} {e} = t

-- off is the number of pis not introducting a forall
{-# TERMINATING #-}
elHS1 : {n : ℕ} (e : Fin (1 N.+ n)) → (t : T n) → Maybe (τ-Hs {HS-UHC} (toℕ (n ℕ- e)))
elHS1 e (set l) = nothing
elHS1 {n} e (v k ∙ x) with (toℕ k) ∸ (toℕ e)
... | p with (ℕ.suc p) ≤? (toℕ (n ℕ- e))
elHS1 e (v k ∙ x) | p | yes p₁ = just (var (fromℕ≤ p₁))
elHS1 e (v k ∙ x) | p | no ¬p = nothing
elHS1 e (def x ∙ xs) with mapM Data.Maybe.monad (elHS1 e) xs
... | xs' = xs' >>= (λ xs'' → just (apps (ty x) xs''))
elHS1 {n} e (π (set l) ⇒ t₁) with elHS1 (inject₁ e) t₁ --(k t₁)
... | p = p >>= λ p' → just (∀' (m {n} {e} p'))-- (m {n} {e} p'))
elHS1 e (π t ⇒ t₁) with elHS1 e t | elHS1 (Fin.suc e) t₁
... | p1 | p2 = p1 >>= λ p1' →
  p2 >>= λ p2' →
  just (p1' ⇒ p2')
elHS1 e (iso x x₁ x₂) with mapM Data.Maybe.monad (elHS1 e) x₁
... | hsArgs = hsArgs >>= λ hsArgs' → just (apps (ty (unquote {!!})) hsArgs')

elHS : (t : T 0) → Maybe (τ-Hs 0)
elHS t = elHS1 {0} Fin.zero t

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

--fTy2 : T 0
--fTy2 = π (set 0) ⇒ (π (def (quote ℕ) ∙ []) ⇒ (π (π (v (fromℕ 1) ∙ []) ⇒ (v (fromℕ 2) ∙ [])) ⇒ (v (fromℕ 2) ∙ []))) -- ⇒ (π (iso vec⇔list List.[ v (fromℕ 2) ∙ [] ] List.[ T.lift (v (fromℕ 1) ∙ []) ]) ⇒ (iso vec⇔list List.[ (v (fromℕ 3) ∙ []) ] List.[ T.lift (v (fromℕ 2) ∙ [] )]))))

fTy3 : T 0
fTy3 = π (iso (quote ℕ⇔ℤ) [] []) ⇒ (iso (quote ℕ⇔ℤ) [] [])

fTy4 : T  0
fTy4 = iso (quote ℕ⇔ℤ) [] []

x : Maybe (τ-Hs ℕ.zero)
x = elHS gTy

g : unquote (elAGDA gTy)
g with x
... | just x' = {!elHS gTy!}
... | nothing = {!!}



--f : unquote (elAGDA fTy)
--f = {!!}
