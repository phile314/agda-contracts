module Foreign.example where

open import Foreign.Base

open Foreign.Base.Fun

module Ta where
  open import Data.List
  open import Reflection

  postulate notImpl : {A : Set} → A

  wayArg : Arg Term
  wayArg = (arg (arg-info hidden relevant) (quoteTerm FFIWay.HS-UHC))

  

  fromTy : List Term → Term → Term
  fromTy env (var x []) = con (quote τ-Hs.var) (wayArg
         ∷ arg (arg-info visible relevant) (lit (nat x))
         ∷ [])
  fromTy env (con c args) = {!!}
  fromTy env (def f args) = def (quote ty) (wayArg
         ∷ {!!}
         ∷ {!!}
         ∷ [])
  fromTy env (app t args) = {!!}
  fromTy env (lam v t) = {!!}
  fromTy env (pat-lam cs args) = {!!}
  fromTy env (pi (arg i (el s t)) (abs s₁ (el _ x₁))) = con (quote _⇒_) (wayArg
         ∷ arg (arg-info visible relevant) (fromTy env t)
         ∷ arg (arg-info visible relevant) (fromTy env x₁)
         ∷ [])
  fromTy env (sort s) = {!!}
  fromTy env (lit l) = {!!}
  fromTy env (quote-goal t) = {!!}
  fromTy env (quote-term t) = {!!}
  fromTy env quote-context = {!!}
  fromTy env (unquote-term t args) = {!!}
  fromTy env unknown = {!!}
  fromTy _ _ = notImpl

module Ex1 where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  {-# COMPILED_DATA_UHC List __LIST__ __NIL__ __CONS__ #-}

  blub : Data.ForeignData (quote List)
  blub = record { foreign-spec = Data.HS-UHC "Data.List.List" (quote List) }


--  head : ∀ {a} → List a → a
--    using foreign (record { foreign-spec = (HS-UHC "Prelude.head" (∀' (( ty (quote List) (Data.ForeignData.foreign-spec blub) ) ⇒ (var 0)) )) } )

module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Foreign.Fancy
  open import Data.Maybe
  open import Data.Product
  open import Data.List
  open Foreign.Base.HS
  import Level

{-  instance
    bla : Data.ForeignData (quote ℤ)
    bla = record { foreign-spec = Data.HS-UHC "Integer" (quote ℤ)}-}

  postulate
    ℤ⇒HSInteger : ℤ → HSInteger
    HSInteger⇒ℤ : HSInteger → ℤ
  {-# COMPILED_UHC ℤ⇒HSInteger UHC.Agda.Builtins.primAgdaIntegerToHsInteger #-}
  {-# COMPILED_UHC HSInteger⇒ℤ UHC.Agda.Builtins.primHsIntegerToAgdaInteger #-}

  ℕ⇔ℤ : PartIsoInt
  ℕ⇔ℤ = toIntPartIso partIso (quote partIso) (quoteTerm partIso) (quoteTerm HSInteger-FD)
    where f : HSInteger → Maybe ℕ
          f i with HSInteger⇒ℤ i
          ... | -[1+ n ] = nothing
          ... | (+ n) = just n
          g : ℕ → HSInteger
          g n = ℤ⇒HSInteger (+ n)
          partIso : PartIso
          partIso = mkPartIso [] [] (record { HSₜ = HSInteger ; other = ℕ , ((withMaybe f) , (total (g))) })

  

-- the special type syntax for using isomorpisms.
--  fty : Set
--  fty = ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩

  -- the internal AST representation of the above notation
  addType : T {Level.zero} 0
  addType = π ( iso ℕ⇔ℤ [] [] ) ⇒ (π (iso ℕ⇔ℤ [] []) ⇒ (iso ℕ⇔ℤ [] []))
--  addType = π ( def_∙_ (quote ℤ) {quote bla} [] ) ⇒ (π (def_∙_ (quote ℤ) {quote bla} []) ⇒ (def_∙_ (quote ℤ) {quote bla} []))

  -- the ffi declaration, which has the type ℤ → ℤ → ℤ
  -- this is not terribly interesting....
  add' : unquote (getAgdaLowType addType)
    using foreign (record { foreign-spec = (HS-UHC "UHC.Agda.Builtins.primHsAdd" (unquote (getFFI addType)))})

  -- the wrapper, which has the type ℕ → ℕ → ℕ
  -- this is the thing we want in the end.
  -- The ffi-lift function does the heavy lifting,
  -- by producing a term which inserts the contracts checks where necessary.
  add : unquote (getAgdaHighType addType)
  add = unquote (ffi-lift addType (quote add'))

open import IO
import IO.Primitive
open import Data.Unit
open import Data.Nat.Show

open Ex2

main : IO.Primitive.IO ⊤
main = run (putStrLn (show k))
  where k = add 12 45


module T3 where
  open import Foreign.Fancy
  open import Data.Nat as N
  open import Level
  
{-  ⟨_∙_⟩ : ∀ {l} → PartIsoInt {l} → List ? → Set l
  ⟨ p ⟩ = {!!}
-}
  open import Data.List as L
  open import Data.Vec
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Data.Product

  instance
    HSList-FD : Data.ForeignData (quote List)
    HSList-FD = record { foreign-spec = Data.HS-UHC "Data.List.List" (quote List) }
  
  list⇒vec : ∀ {l} {n : ℕ} {A : Set l} → List A → Maybe (Vec A n)
  list⇒vec {_} {n} xs with n N.≟ L.length xs
  list⇒vec xs | yes refl = just (Data.Vec.fromList xs)
  list⇒vec xs | no ¬p = nothing

  vec⇔list : (l : Level) → PartIsoInt {l}
  vec⇔list l = toIntPartIso partIso (quote partIso) (quoteTerm partIso) {{HSList-FD}} (quoteTerm HSList-FD)
    where
    partIso : PartIso
    partIso = mkPartIso L.[ Set l ] L.[ (Lift ℕ) ]
      (λ a → record
        { HSₜ = L.List a
        ; other = λ n → (Vec a (lower n)) , ( withMaybe list⇒vec , Conversion.total Data.Vec.toList)})

  getArgs : ∀ {l} → PartIsoInt {l} → Set (Level.suc l)
  getArgs p = WithArgs ((PartIso.ALLₐ h) L.++ ( PartIso.AGDAₐ h))
    where h = PartIsoInt.wrapped p

  data AST {l m} : Set (Level.suc (Level.suc (l Level.⊔ m )))

  getTy : ∀ {l} → AST {l} {l} → Set l --(l Level.⊔ m )

  data AST {l m} where
    pi : (a : AST {l} {l}) → (getTy a → AST {m} {m}) → AST
    ⟦_⟧ : (A : Set l) → AST -- normal type (List, Nat, etc..)
    ⟦_⇋_⟧ : (pi : PartIsoInt {l}) → getArgs pi → AST -- isomorphism

  split++ : ∀ {l} {a : ArgTys {l}} → {b : ArgTys {l}} → (args : WithArgs (a L.++ b)) → (WithArgs a × WithArgs b)
  split++ {a = []} args = [] , args
  split++ {a = x ∷ a} (a₁ , args) = (a₁ , (proj₁ r)) , (proj₂ r)
    where r = split++ args

  getTy (pi a x) = (arg : getTy a) → (getTy (x arg))
  getTy (⟦ x ⟧) = x
  getTy (⟦ x ⇋ x₁ ⟧) = proj₁ (applyArgs (PartIso'.other g) (proj₂ k)) --(PartIso.iso h) x₁
    where h = PartIsoInt.wrapped x
          k = split++ {_} {PartIso.ALLₐ h} x₁
          g = applyArgs (PartIso.iso h) (proj₁ k)

  id : ∀ {a} {A : Set a} → A → A
  id x = x

  syntax pi e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇒ e₂
  syntax id e = ⟨ e ⟩

  -- an example how the contracts syntax could look like,
  -- if implemented using normal Agda constructs.
  ty' : AST
  ty' = ⟨ a ∷ ⟦ Set ⟧ ⟩⇒
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
    ⟨ y ∷ ⟦ vec⇔list Level.zero ⇋ a , ((lift x) , []) ⟧ ⟩⇒
    ⟨ xs ∷ ⟦ List a ⟧ ⟩⇒
    ⟨ ⟦ List a ⟧ ⟩

  open import Reflection
--  f : Term
--  f = quoteTerm ( ⟨ n ∷ ℕ ⟩⇒ ( ⟨ x ∷ ℕ ⟩⇒ ⟨ (vec⇔list Level.zero ⇄ cons n nil) ⟩ ) )

  g : {! definition (quote ty')!}
  g = {!!}

  postulate mkForeign : {a : Set} → a

--  q : ℕ → ℕ
--  q = tactic t

  q' : ℕ → ℕ
  q' = quoteGoal g in unquote {!g!}

--  r : ℕ → ℕ
--    using foreign (record {})

module ReflTest where

  open import Reflection
  open import Data.List
  open import Foreign.Base
  open Foreign.Base.Data
  open Foreign.Base.Fun
  open import Function

  unArg : Arg Term → Term
  unArg (arg i x) = x

  postulate IMPOSSIBLE : {A : Set} → A

  {-# TERMINATING #-}
  xTy : Term → List Name
  xTy (var x args) = concat (map (xTy ∘ unArg) args)
  xTy (con c args) = IMPOSSIBLE
  xTy (def f args) =  f ∷ (concat (map (xTy ∘ unArg) args))
  xTy (app t args) = IMPOSSIBLE
  xTy (lam v t) = IMPOSSIBLE -- can this actually happen? Anyway, Haskell doesn't supprt lambdas in types, so just fail
  xTy (pat-lam cs args) = IMPOSSIBLE
  xTy (pi (arg i (el s t)) (abs s₁ (el s₂ t₁))) = xTy t ++ xTy t₁
  xTy (sort s) = []
  xTy (lit l) = IMPOSSIBLE
  xTy (quote-goal t) = IMPOSSIBLE
  xTy (quote-term t) = IMPOSSIBLE
  xTy quote-context = IMPOSSIBLE
  xTy (unquote-term t args) = IMPOSSIBLE
  xTy unknown = IMPOSSIBLE

  xTy' : Term → Set
  xTy' t = g ns
    where
      ns = xTy t
      g : List Name → Set
      g [] = τ-Hs HS-UHC
      g (x ∷ xs) = {{ fd : ForeignData x }} → g xs

  x : (t : Term) → xTy' t
  x (var x args) = {!!}
  x (con c args) = IMPOSSIBLE
  x (def f args) = λ {{fd}} → {!!} -- τ-Hs.ty f (ForeignData.foreign-spec fd) --(τ-Hs.ty {!τ-Hs.ty!} )
  x (app t args) = {!!}
  x (lam v t) = {!!}
  x (pat-lam cs args) = {!!}
  x (pi (arg i x) t₂) = {!!} -- here we need to check if t₁ is of type set.
  x (sort s) = {!!}
  x (lit l) = IMPOSSIBLE
  x (quote-goal t) = IMPOSSIBLE
  x (quote-term t) = IMPOSSIBLE
  x quote-context = IMPOSSIBLE
  x (unquote-term t args) = IMPOSSIBLE
  x unknown = IMPOSSIBLE
--  x _ = {!!}

  open import Data.Nat
  open import Data.Integer
  open Foreign.Base.HS
  k : Set
  k = ℤ

  m : τ-Hs HS-UHC
  m = x (quoteTerm HSInteger)

  y : {!quoteTerm ( { a : Set} → a )!}
  y = {!!}
