{-# OPTIONS --type-in-type #-}

module Contracts.SSyn where


-- surface syntax tests
module T3 where
  open import Contracts.Base
  open import Data.Nat as N
  open import Level
  
{-  ⟨_∙_⟩ : ∀ {l} → PartIsoInt {l} → List ? → Set l
  ⟨ p ⟩ = {!!}
-}
  open import Data.List as List
  open import Data.Vec
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Data.Product

  data _Level≤_ : Level → Level → Set where
    Z : {m : Level} → Level.zero Level≤ m
    S : {m n : Level} → m Level≤ n → (Level.suc m) Level≤ (Level.suc n)

  record PartIsoPub : Set where
    constructor mkIsoPub
    field partIso : PartIso
    field partIsoInt : PartIsoInt

  getArgs : PartIsoPub → Set
  getArgs p = WithArgs ((PartIso.LOWₐ h) List.++ ( PartIso.HIGHₐ h))
    where h = PartIsoPub.partIso p --PartIsoInt.wrapped p

  data AST : Set

  getTy : AST → Set

  data AST where
    pi : (a : AST) → ArgWay → (getTy a → AST) → AST
    ⟦_⟧ : (A : Set) → AST -- normal type (List, Nat, etc..)
    ⟦_⇋_⟧ : (pi :  PartIsoPub) → getArgs pi → AST -- isomorphism

  split++ : {a : ArgTys} → {b : ArgTys} → (args : WithArgs (a List.++ b)) → (WithArgs a × WithArgs b)
  split++ {a = []} args = [] , args
  split++ {a = x ∷ a} (a₁ , args) = (a₁ , (proj₁ r)) , (proj₂ r)
    where r = split++ args

  getTy (pi a _ x) = (arg : getTy a) → (getTy (x arg))
  getTy (⟦ x ⟧) = x
--  getTy {l} (⟦Set_⟧ ll {lt}) = {!!} --Lift {Level.suc ll} {l} (Set ll)
  getTy (⟦ x ⇋ x₁ ⟧) = proj₁ (applyArgs (proj₂ g) (proj₂ k)) --(PartIso.iso h) x₁
    where h = PartIsoPub.partIso x --PartIsoInt.wrapped x
          k = split++ {PartIso.LOWₐ h} {_} x₁
          g = applyArgs (PartIso.iso h) (proj₁ k)

  id : {A : Set} → A → A
  id x = x

  piK : (a : AST) → (getTy a → AST) → AST
  piK x = pi x Keep
  piD : (a : AST) → (getTy a → AST) → AST
  piD x = pi x Discard
  
  syntax piK e₁ (λ x → e₂) = ⟨ x ∷ e₁ ⟩⇒ e₂
  syntax piD e₁ (λ x → e₂) = ⟨ x ↛∷ e₁ ⟩⇒ e₂
  syntax id e = ⟨ e ⟩

  kl : ℕ → ℕ
  kl = quoteGoal g in {!!}


  kkk : _
  kkk = kl

  mm : {!!}
  mm = {!!}

  -- an example how the contracts syntax could look like,
  -- if implemented using normal Agda constructs.
{-  ty' : AST
  ty' = ⟨ a ∷ ⟦ Set₁ ⟧ ⟩⇒
    ⟨ x ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
    ⟨ y ∷ ⟦ vec⇔list ⇋ lift a , ((lift x) , []) ⟧ ⟩⇒
    ⟨ xs ∷ ⟦ List a ⟧ ⟩⇒
    ⟨ ⟦ List a ⟧ ⟩-}

  postulate Errrr Errrr2 Errrr3 : {A : Set} → A

{-  open import Function
  open import Reflection as R
  f' : AST
  f' = ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ Set ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ lift ℕ , lift n , [] ⟧ ⟩
  f : Term
  f = quoteTerm (⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ x ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ ⟦ vec⇔list ⇋ lift ℕ , lift n , [] ⟧ ⟩)


  ff : Term
  ff = quoteTerm k
    where
      k : AST
      k = ⟨ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩

  gg : Term
  gg = quoteTerm ( ⟨ n ∷ ⟦ ℕ ⟧ ⟩⇒ ⟨ ⟦ ℕ ⟧  ⟩ )

  unArg : ∀ {A} → Arg A → A
  unArg (arg i x) = x

  getLevel : Term → Level
  getLevel t = Level.zero

  stripLam : Term → Term
  stripLam (lam v (abs s x)) = x
  stripLam _ = Errrr2

  defToNm : Term → Name
  defToNm (def nm []) = nm
  defToNm _ = error

  pubIsoToIntIsoNm : Term → Name
  pubIsoToIntIsoNm (con (quote mkIsoPub) args) = case (unArg $ lookup' 2 args) of (
    λ {(con (quote mkIsoInt) args') → case unArg $ lookup' 0 args' of (
      λ { (lit (name nm)) → nm ;
          _ → error});
       _ → error
      })
  pubIsoToIntIsoNm _ = error

  {-# TERMINATING #-}
  withArgsToT' : {n : ℕ} → Term → List (T n)
  ast-ty⇒T' : ∀ {n} → (t : Term) → T n

  withArgsToT' {n} (con (quote WithArgs.[]) _) = []
  withArgsToT' {n} (con (quote WithArgs._,_) args') = arg' ∷ withArgsToT' {n} tl
    where
      hd = unArg $ lookup' 2 args' -- con lift ...
      tl = unArg $ lookup' 4 args'
      arg' : T n
      arg' = case hd of (
        λ { (con (quote Level.lift) args') → ast-ty⇒T' (unArg $ lookup' 3 args') ;
            _ → Errrr3 })
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
  ast⇒T' (con c args) = case c of (
    -- todo extract KEEP
    λ { (quote AST.pi) → π ast⇒T' (unArg (lookup' 2 args)) ∣ Keep ⇒ ast⇒T' ((stripLam ∘ unArg ∘ lookup' 4) args) ;
        (quote AST.⟦_⟧) → ast-ty⇒T' (unArg (lookup' 2 args)) ;
        (quote AST.⟦_⇋_⟧) → iso (record { wrappedₙ = pubIsoToIntIsoNm $ unArg $ lookup' 2 args}) (withArgsToT' {!!}) {!!} ; --iso ? ? ? --(record { wrapped = ((unArg (lookup' 2 args)))}) [] [] ;
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

  g : {! getTy f'!}
  g = {!ast⇒T' f!}

  open import Data.Integer
  addImpl' : ℤ → ℤ → ℤ
  addImpl' a b = a Data.Integer.+ b

  addContr : Term
  addContr = quoteTerm (
        ⟨ a ∷ ⟦ ℤ ⟧ ⟩⇒ --⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
        ⟨ b ∷ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩⇒
        ⟨ ⟦ ℕ⇔ℤ ⇋ [] ⟧ ⟩ )
--        ⟨ ⟦ vec⇔list ⇋ lift ℕ , lift n , [] ⟧ ⟩ )

--  add : unquote (getAgdaHighType (ast⇒T' addContr))
--  add = unquote (ffi-lift (ast⇒T' addContr) (quote addImpl'))


  
  open import Data.Bool
  lk : Bool → Term
  lk true = let x = {!open import Data.List!} in {!!}
  lk false = {!add ( -[1+ 30 ] ) (24)!}
    where open import Data.List public

  postulate mkForeign : {a : Set} → a
-}
--  q : ℕ → ℕ
--  q = tactic t

--  q' : ℕ → ℕ
--  q' = quoteGoal g in unquote {!g!}

--  r : ℕ → ℕ
--    using foreign (record {})
