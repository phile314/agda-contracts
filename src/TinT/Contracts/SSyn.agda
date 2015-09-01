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
  getArgs p = WithArgs ((List.map (λ a → WContext a L) ( PartIso.LOWₐ h)) List.++
    (List.map (λ x → WContext x H) (PartIso.HIGHₐ h)))
    where h = PartIsoPub.partIso p --PartIsoInt.wrapped p
    
  withArgs : List Set → Set
  withArgs as = WithArgs as

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

  split++ : {a : ArgTys} → {b : ArgTys} → (args : WithArgs (a List.++ b)) → (WithArgs a × WithArgs b)
  split++ {a = []} args = [] , args
  split++ {a = x ∷ a} (a₁ , args) = (a₁ , (proj₁ r)) , (proj₂ r)
    where r = split++ args

  unconArgs : {args : ArgTys} {f : Set → Set} {f' : {A : Set} → f A → A} → WithArgs (List.map f args) → WithArgs args
  unconArgs {[]} [] = []
  unconArgs {x ∷ args} {f} {f'} (a , wa) = f' a , unconArgs {f' = f'} wa

  getTy (pi {p} a aw x) = (arg : (withWCon (pos+way→Context p aw) (getTy a))) → (getTy (x arg))
  getTy (⟦ x ⟧) = x
  -- this should be the pair of low / high args
  getTy (⟦ x ⇋ x₁ ⟧) = WContext (proj₁ g) L × WContext (proj₁ i) H
    where h = PartIsoPub.partIso x
          k = split++ {List.map (λ z → WContext z L) (PartIso.LOWₐ h)} x₁
          g = applyArgs (PartIso.iso h) {-(PartIso.iso h)-} (unconArgs {f' = unC} (proj₁ k))
          i = applyArgs {PartIso.HIGHₐ h} (proj₂ g) (unconArgs {f' = unC} (proj₂ k))

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

  pubIsoToIntIsoNm : Term → Term
  pubIsoToIntIsoNm (con (quote mkIsoPub) args) = case (unArg $ lookup' 1 args) of (
    λ {(con (quote mkIsoInt) args') → {- case-} unArg $ lookup' 0 args' {-of (
      λ { (lit (name nm)) → (def nm []) ;
          _ → error })-} ;
       _ → error
      })
  pubIsoToIntIsoNm _ = error

  pubIsoGetNumArgs : Term → (ℕ × ℕ) -- low, high
  pubIsoGetNumArgs (con (quote mkIsoPub) args) = case (unArg $ lookup' 0 args) of (
    λ { (con (quote mkPartIso) args) → (listLen $ unArg $ lookup' 0 args) , (listLen $ unArg $ lookup' 1 args)
      ; _ → error
      })
  pubIsoGetNumArgs _ = error

  unWCon : Term → Term
  unWCon (con (quote C) args) = unArg $ lookup' 2 args
  unWCon _ = error

  {-# TERMINATING #-}
  withArgsToT' : {n : ℕ} → Term → List (T n)
  ast-ty⇒T' : ∀ {n} → (t : Term) → T n

  withArgsToT' {n} (con (quote WithArgs.[]) _) = []
  withArgsToT' {n} (con (quote WithArgs._,_) args') = arg' ∷ withArgsToT' {n} tl
    where
      hd = unArg $ lookup' 1 args' -- con lift ...
      tl = unArg $ lookup' 3 args'
      arg' : T n
      arg' = ast-ty⇒T' $ unWCon hd
  withArgsToT' _ = Errrr3
  
  open import Data.Fin using (fromℕ≤)
  
  {-# TERMINATING #-}
  ast-ty⇒T' {n} (var x args) = case (ℕ.suc x) ≤? n of (
    λ { (yes p) → var (fromℕ≤ p) ∙ List.map (ast-ty⇒T' ∘ unArg) args
      ; (no _) → Errrr2
      })
  ast-ty⇒T' (def f args) = def f ∙ List.map (ast-ty⇒T' ∘ unArg) args
  ast-ty⇒T' (sort (set t)) = Errrr2
  ast-ty⇒T' (sort (lit n₁)) = set n₁
  ast-ty⇒T' (sort unknown) = Errrr2
  ast-ty⇒T' _ = Errrr2

  {-# TERMINATING #-}
  ast⇒T' : ∀ {n} → (t : Term) -- AST
    → T n
  arg-ast⇒T : ∀ {n} → Arg Term → T n

  ast⇒T' (var x args) = Errrr3
  ast⇒T' {n} (con c args) = case c of (
    -- todo extract KEEP
    λ { (quote AST'.pi) → π ast⇒T' (unArg (lookup' 1 args)) ∣ Keep ⇒ ast⇒T' ((stripLam ∘ unArg ∘ lookup' 3) args) ;
        (quote AST'.⟦_⟧) → ast-ty⇒T' (unArg (lookup' 1 args)) ;
        (quote AST'.⟦_⇋_⟧) →
          let pubIso = unArg $ lookup' 1 args
              nArgs = pubIsoGetNumArgs pubIso
              intIso = record { wrappedₙ = pubIsoToIntIsoNm pubIso }
              allArgs = withArgsToT' (unArg $ lookup' 2 args)
           in iso intIso (List.take (proj₁ nArgs) allArgs) (List.drop (proj₁ nArgs) allArgs) ; --iso ? ? ? --(record { wrapped = ((unArg (lookup' 2 args)))}) [] [] ;
        _ → Errrr3})
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
  ast⇒T' unknown = Errrr3

  arg-ast⇒T (arg i x) = ast⇒T' x

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
