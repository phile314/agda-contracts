{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module Contracts.SSyn where

open import Contracts.Base
open import Data.Product

module Types where

  -- Are we in low/high/common context?
  data Context : Set where
    H : Context
    L : Context
    Common : Context

  data WContext (A : Set) : Context → Set where
    wrap : ∀ {c} → A → WContext A c
  
  private
    unC : ∀ {a c} → WContext a c → a
    unC (wrap x) = x

  record PartIsoPub : Set where
    constructor mkIsoPub
    field partIso : PartIso
    field partIsoInt : PartIsoInt

  getArgs : PartIsoPub → Set
  getArgs p = Σ (PartIso.ARGₐ p') (λ aa → (WContext (PartIso.ARGₗ p' aa) L) × (WContext (PartIso.ARGₕ p' aa) H))
    where p' = PartIsoPub.partIso p

  pos+way→Context : Position → ArgWay → Context
  pos+way→Context p Keep = Common
  pos+way→Context Neg Discard = H
  pos+way→Context Pos Discard = L

  withWCon : Context → Set → Set
  withWCon Common s = s
  withWCon c s = WContext s c
  

  data C' : Position → Set
  getTy : ∀ {p} → C' p → Set

  data C' where
    pi : ∀ {p} → (a : C' p) → (aw : ArgWay)
      → (withWCon (pos+way→Context p aw) (getTy a) → C' (invertPosition p))
      → C' (invertPosition p)
    ⟦_⟧ : ∀ {p} (A : Set) → C' p -- normal type (List, Nat, etc..)
    ⟦_⇋_⟧ : ∀ {p} (pi :  PartIsoPub) → getArgs pi → C' p -- isomorphism


  getTy (pi {p} a aw x) = (arg : (withWCon (pos+way→Context p aw) (getTy a))) → (getTy (x arg))
  getTy (⟦ x ⟧) = x
  -- this should be the pair of low / high args
  getTy (⟦ p ⇋ (aₐ , (aₗ , aₕ)) ⟧) = WContext (PartIso.τₗ p' aₐ (unC aₗ)) L × WContext (PartIso.τₕ p' aₐ (unC aₕ)) H
    where p' = PartIsoPub.partIso p

  C = C' Pos




module Reflect where
  open Types
  open import Data.Nat as N
  open import Level
  
  open import Data.List as List
  open import Data.Vec hiding (_>>=_)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  open import Reflection
  open import Function

  unArg : ∀ {A} → Arg A → A
  unArg (arg i x) = x

  private
    postulate
      InvalidContract : ∀ {a} → a
      InternalError : ∀ {a} → a

  fromJust : ∀ {A} → Maybe A → A
  fromJust (just x) = x
  fromJust nothing = InternalError

  stripLam : Term → Term
  stripLam (lam v (abs s x)) = x
  stripLam (pat-lam cs args) = InternalError
  stripLam (quote-goal _ ) = InternalError
  -- there is no lambda, which means we just got a partially applied function
  stripLam t = fromJust $ (λ x → applyTerm x List.[ arg def-argInfo (var 0 []) ]) <$> maybeSafe t'
    where
      open import Category.Monad
      open RawMonad (Data.Maybe.monad {Level.zero})
      open import Reflection.DeBruijn
      open import Reflection.Substitute
      open import Data.Unit
      t' = weaken 1 t

  defToNm : Term → Name
  defToNm (def nm []) = nm
  defToNm _ = InternalError

  listLen : Term → ℕ
  listLen t = case t of (
    λ { (con (quote Data.List.Base.List.[]) args) → 0
      ; (con (quote List._∷_) args) → N.suc (listLen (unArg $ lookup' 3 args))
      ; _ →  InternalError
      })
    where open import Data.List.Base

  pubIsoToIntIso : Term → Term
  pubIsoToIntIso (con (quote mkIsoPub) args) = case (unArg $ lookup' 1 args) of (
    λ {(con (quote mkIsoInt) args') →  unquote-term (unArg $ lookup' 0 args') []
      ; _ → InternalError
      })
  pubIsoToIntIso _ = InternalError

  pubIsoGetNumArgs : Term → (ℕ × ℕ) -- low, high
  pubIsoGetNumArgs (con (quote mkIsoPub) args) = case (unArg $ lookup' 0 args) of (
    λ { (con (quote mkPartIso) args) → (listLen $ unArg $ lookup' 0 args) , (listLen $ unArg $ lookup' 1 args)
      ; _ → InternalError
      })
  pubIsoGetNumArgs _ = InternalError

  unWCon : Term → Term
  -- an argument get's lifted here into high/low context
  unWCon (con (quote wrap) args) = unArg $ lookup' 2 args
  -- argument was already in low/high context
  unWCon t = t


  -- splits an argument term into the all/low/high arg terms
  splitArgs : Term → Term × Term × Term
  splitArgs (con (quote _,_) args) =
    (unArg $ lookup' 4 args) ,
    (case (unArg $ lookup' 5 args) of λ
      { (con (quote _,_) args) → (unWCon $ unArg $ lookup' 4 args) , (unWCon $ unArg $ lookup' 5 args)
      ; _ → InternalError
      })
  splitArgs _ = InternalError

  ast⇒ArgWay : Term → ArgWay
  ast⇒ArgWay (con (quote Keep) args) = Keep
  ast⇒ArgWay (con (quote Erase) args) = Erase
  ast⇒ArgWay _ = InternalError

  surface⇒internal : ∀ {n} → (t : Term) -- AST
    → InternalSyn n
  arg-surface⇒internal : ∀ {n} → Arg Term → InternalSyn n

  -- Converts the quoted SSyn AST to the internal AST.
  -- We assume that the quoted SSyn AST is valid Agda code with type AST'.
  surface⇒internal (var x args) = InternalError
  surface⇒internal {n} (con c args) = case c of (
    λ { (quote C'.pi) → let k = ast⇒ArgWay $ unArg $ lookup' 2 args
               in π surface⇒internal (unArg (lookup' 1 args)) ∣ k ⇒ surface⇒internal ((stripLam ∘ unArg ∘ lookup' 3) args) ;
        (quote C'.⟦_⟧) → agda-ty (unArg (lookup' 1 args)) ;
        (quote C'.⟦_⇋_⟧) →
          let pubIso = unArg $ lookup' 1 args
              nArgs = pubIsoGetNumArgs pubIso
              intIso = record { wrapped = pubIsoToIntIso pubIso }
              (aa , al , ah) = splitArgs $ unArg $ lookup' 2 args
           in iso intIso aa al ah
      ; _ → InternalError
      })
  surface⇒internal (def f args) = InternalError
  surface⇒internal (lam v t) = InternalError
  surface⇒internal (pat-lam cs args) = InternalError
  surface⇒internal (pi t₁ t₂) = InternalError
  surface⇒internal (sort s) = InternalError
  surface⇒internal (lit l) = InternalError
  surface⇒internal (quote-goal t) = InternalError
  surface⇒internal (quote-term t) = InternalError
  surface⇒internal quote-context = InternalError
  surface⇒internal (unquote-term t args) = InternalError
  surface⇒internal (foreign-term t ty) = InternalError
  surface⇒internal unknown = InternalError

  arg-surface⇒internal (arg i x) = surface⇒internal x

module Syntax where
  open Types
  open Reflect

  id : {A : Set} → A → A
  id x = x

  piK : ∀ {p} (a : C' p) → (getTy a → C' (invertPosition p)) → C' (invertPosition p)
  piK x = pi x Keep
  piD : ∀ {p} (a : C' p) → (withWCon (pos+way→Context p Erase) (getTy a) → C' (invertPosition p)) → C' (invertPosition p)
  piD x = pi x Erase
  
  syntax piK e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇒ e₂
  syntax piD e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇏ e₂
  syntax id e = ⟨ e ⟩
  infixl 10 piK
  infixl 10 piD
  infixl 10 id

  open import Data.Unit
  ∅ : ⊤ × WContext ⊤ L × WContext ⊤ H
  ∅ = tt , ((wrap tt) , (wrap tt))

  open import Reflection
  open import Data.List
  open import Contracts.Base

  forceTy : (A : Set) → A → A
  forceTy _ x = x

  forceTy' : Term → Term → Term
  forceTy' ty val =
    def (quote forceTy)
      ( arg (arg-info visible relevant) ty
      ∷ arg (arg-info visible relevant) val
      ∷ [])

  makeContract = forceTy C

  macro
    assert : (ast : Term) -- AST
      →  (lowDef : Term)
      → Term
    assert ast lowDef = forceTy' (deriveHighType int) lifted
      where
        open import Function
        int = surface⇒internal ast
        low = forceTy' (deriveLowType int) lowDef
        lifted = contract-apply int low


open Syntax public
-- hide constructor!
open Types public hiding (wrap)

wrap : ∀ {A c} → A → WContext A c
wrap = WContext.wrap

