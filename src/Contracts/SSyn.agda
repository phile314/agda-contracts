{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module Contracts.SSyn where


-- surface syntax tests
module T3 where
  open import Contracts.Base
  open import Data.Nat as N
  open import Level
  
  open import Data.List as List
  open import Data.Vec hiding (_>>=_)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Data.Product

  data Context : Set where
    H : Context
    L : Context
    Both : Context


  data WContext (A : Set) : Context → Set where
    C : ∀ {c} → A → WContext A c

  liftW : ∀ {c} {A : Set} → A → WContext A c
  liftW x = C x
  
  private
    unC : ∀ {a c} → WContext a c → a
    unC (C x) = x

  record PartIsoPub : Set where
    constructor mkIsoPub
    field partIso : PartIso
    field partIsoInt : PartIsoInt

  getArgs : PartIsoPub → Set
  getArgs p = Σ (PartIso.ARGₐ p') (λ aa → (WContext (PartIso.ARGₗ p' aa) L) × (WContext (PartIso.ARGₕ p' aa) H))
    where p' = PartIsoPub.partIso p

  pos+way→Context : Position → ArgWay → Context
  pos+way→Context p Keep = Both
  pos+way→Context Neg Discard = H
  pos+way→Context Pos Discard = L

  withWCon : Context → Set → Set
  withWCon Both s = s
  withWCon c s = WContext s c
  

  data AST' : Position → Set
  getTy : ∀ {p} → AST' p → Set

  data AST' where
    pi : ∀ {p} → (a : AST' p) → (aw : ArgWay)
      → (withWCon (pos+way→Context p aw) (getTy a) → AST' (invertPosition p))
      → AST' (invertPosition p)
    ⟦_⟧ : ∀ {p} (A : Set) → AST' p -- normal type (List, Nat, etc..)
    ⟦_⇋_⟧ : ∀ {p} (pi :  PartIsoPub) → getArgs pi → AST' p -- isomorphism


  getTy (pi {p} a aw x) = (arg : (withWCon (pos+way→Context p aw) (getTy a))) → (getTy (x arg))
  getTy (⟦ x ⟧) = x
  -- this should be the pair of low / high args
  getTy (⟦ p ⇋ (aₐ , (aₗ , aₕ)) ⟧) = WContext (PartIso.τₗ p' aₐ (unC aₗ)) L × WContext (PartIso.τₕ p' aₐ (unC aₕ)) H
    where p' = PartIsoPub.partIso p

  AST = AST' Pos

  id : {A : Set} → A → A
  id x = x

  piK : ∀ {p} (a : AST' p) → (getTy a → AST' (invertPosition p)) → AST' (invertPosition p)
  piK x = pi x Keep
  piD : ∀ {p} (a : AST' p) → (withWCon (pos+way→Context p Discard) (getTy a) → AST' (invertPosition p)) → AST' (invertPosition p)
  piD x = pi x Discard
  
  syntax piK e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇒ e₂
  syntax piD e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇏ e₂
  syntax id e = ⟨ e ⟩
  infixl 10 piK
  infixl 10 piD
  infixl 10 id

  postulate Errrr Errrr2 Errrr3 : {A : Set} → A

  open import Reflection
  open import Function

  unArg : ∀ {A} → Arg A → A
  unArg (arg i x) = x

  getLevel : Term → Level
  getLevel t = Level.zero

  fromJust : ∀ {A} → Maybe A → A
  fromJust (just x) = x
  fromJust nothing = error

  stripLam : Term → Term
  stripLam (lam v (abs s x)) = x
  stripLam (pat-lam cs args) = error
  stripLam (quote-goal _ ) = error
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
  defToNm _ = error

  listLen : Term → ℕ
  listLen t = case t of (
    λ { (con (quote Data.List.Base.List.[]) args) → 0
      ; (con (quote List._∷_) args) → N.suc (listLen (unArg $ lookup' 3 args))
      ; _ →  Errrr
      })
    where open import Data.List.Base

  pubIsoToIntIso : Term → Term
  pubIsoToIntIso (con (quote mkIsoPub) args) = case (unArg $ lookup' 1 args) of (
    λ {(con (quote mkIsoInt) args') →  unquote-term (unArg $ lookup' 0 args') []
      ; _ → error
      })
  pubIsoToIntIso _ = error

  pubIsoGetNumArgs : Term → (ℕ × ℕ) -- low, high
  pubIsoGetNumArgs (con (quote mkIsoPub) args) = case (unArg $ lookup' 0 args) of (
    λ { (con (quote mkPartIso) args) → (listLen $ unArg $ lookup' 0 args) , (listLen $ unArg $ lookup' 1 args)
      ; _ → error
      })
  pubIsoGetNumArgs _ = error

  unWCon : Term → Term
  -- an argument get's lifted here into high/low context
  unWCon (con (quote C) args) = unArg $ lookup' 2 args
  -- argument was already in low/high context
  unWCon t = t


  -- splits an argument term into the all/low/high arg terms
  splitArgs : Term → Term × Term × Term
  splitArgs (con (quote _,_) args) =
    (unArg $ lookup' 4 args) ,
    (case (unArg $ lookup' 5 args) of λ
      { (con (quote _,_) args) → (unWCon $ unArg $ lookup' 4 args) , (unWCon $ unArg $ lookup' 5 args)
      ; _ → Errrr2
      })
  splitArgs _ = Errrr2

  ast⇒ArgWay : Term → ArgWay
  ast⇒ArgWay (con (quote Keep) args) = Keep
  ast⇒ArgWay (con (quote Discard) args) = Discard
  ast⇒ArgWay _ = error

  open import Data.Fin using (fromℕ≤)


  ast-ty⇒T' : ∀ {n} → (t : Term) → T n
  ast-ty⇒T' {n} (var x args) = case (ℕ.suc x) ≤? n of (
    λ { (yes p) → var (fromℕ≤ p) ∙ List.map (ast-ty⇒T' ∘ unArg) args
      ; (no _) → Errrr3
      })
  ast-ty⇒T' (def f args) = def f ∙ List.map (ast-ty⇒T' ∘ unArg) args
  ast-ty⇒T' (sort (set t)) = Errrr3
  ast-ty⇒T' (sort (lit n₁)) = set n₁
  ast-ty⇒T' (sort unknown) = Errrr2
  ast-ty⇒T' _ = Errrr3


  {-# TERMINATING #-}
  ast⇒T' : ∀ {n} → (t : Term) -- AST
    → T n
  arg-ast⇒T : ∀ {n} → Arg Term → T n

  ast⇒T' (var x args) = Errrr3
  ast⇒T' {n} (con c args) = case c of (
    λ { (quote AST'.pi) → let k = ast⇒ArgWay $ unArg $ lookup' 2 args
               in π ast⇒T' (unArg (lookup' 1 args)) ∣ k ⇒ ast⇒T' ((stripLam ∘ unArg ∘ lookup' 3) args) ;
        (quote AST'.⟦_⟧) → ast-ty⇒T' (unArg (lookup' 1 args)) ;
        (quote AST'.⟦_⇋_⟧) →
          let pubIso = unArg $ lookup' 1 args
              nArgs = pubIsoGetNumArgs pubIso
              intIso = record { wrapped = pubIsoToIntIso pubIso }
              (aa , al , ah) = splitArgs $ unArg $ lookup' 2 args --withArgsToT' (unArg $ lookup' 2 args)
           in iso intIso aa al ah --iso intIso (List.take (proj₁ nArgs) allArgs) (List.drop (proj₁ nArgs) allArgs) ;
      ; _ → Errrr3
      })
  ast⇒T' (def f args) = Errrr3
  ast⇒T' (lam v t) = Errrr3
  ast⇒T' (pat-lam cs args) = Errrr3
  ast⇒T' (pi t₁ t₂) = Errrr3
  ast⇒T' (sort s) = Errrr3
  ast⇒T' (lit l) = Errrr3
  ast⇒T' (quote-goal t) = Errrr3
  ast⇒T' (quote-term t) = Errrr3
  ast⇒T' quote-context = Errrr3
  ast⇒T' (unquote-term t args) = Errrr3
  ast⇒T' (foreign-term t ty) = Errrr3
  ast⇒T' unknown = Errrr3

  arg-ast⇒T (arg i x) = ast⇒T' x

  open import Data.Unit
  ∅ : ⊤ × WContext ⊤ L × WContext ⊤ H
  ∅ = tt , ((liftW tt) , (liftW tt))

open T3 public

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

makeContract = forceTy AST

macro
  assert : (ast : Term) -- AST
    →  (lowDef : Term)
    → Term
  assert ast lowDef = forceTy' (getAgdaHighType t) lifted
    where
      open import Function
      t = ast⇒T' {0} ast
      low = forceTy' (getAgdaLowType t) lowDef
      lifted = ffi-lift t low

