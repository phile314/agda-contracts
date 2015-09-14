module Contracts.example where

module NatIntIso where
  open import Contracts.Base
  open import Data.Nat
  open import Data.Integer
  open import Data.Maybe
  open import Data.List
  open import Data.Product
  
  ℕ⇔ℤI : PartIso
  ℕ⇔ℤI = mkPartIso [] [] (ℤ , (ℕ , ((withMaybe f) , (total (ℤ.+_)))))
    where f : ℤ → Maybe ℕ
          f -[1+ n ] = nothing
          f (+ n) = just n

  ℕ⇔ℤ' : PartIsoInt
  ℕ⇔ℤ' = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrappedₙ = quote ℕ⇔ℤI } --; wrapped = partIso}


module Ex2 where
  open import Data.Nat
  open import Data.Integer
  open import Contracts.Base
  open import Data.Maybe
  open import Data.Product
  open import Data.List
  open import Data.Vec
  open NatIntIso
  import Level


-- the special type syntax for using isomorpisms.
--  fty : Set
--  fty = ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩ → ⟨ ℕ⇔ℤ ⟩

  -- the internal AST representation of the above notation
  addType : T 0
  addType = π ( iso ℕ⇔ℤ' [] [] ) ∣ Keep ⇒ (π (iso ℕ⇔ℤ' [] []) ∣ Keep ⇒ (iso ℕ⇔ℤ' [] []))
--  addType = π ( def_∙_ (quote ℤ) {quote bla} [] ) ⇒ (π (def_∙_ (quote ℤ) {quote bla} []) ⇒ (def_∙_ (quote ℤ) {quote bla} []))

  -- the ffi declaration, which has the type ℤ → ℤ → ℤ
  -- this is not terribly interesting....
--  add' : unquote (getAgdaLowType addType)
--    using foreign (record { foreign-spec = (HS-UHC "UHC.Agda.Builtins.primHsAdd" (unquote (getFFI addType)))})
  add' : ℤ → ℤ → ℤ
  add' = Data.Integer._+_

  -- the wrapper, which has the type ℕ → ℕ → ℕ
  -- this is the thing we want in the end.
  -- The ffi-lift function does the heavy lifting,
  -- by producing a term which inserts the contracts checks where necessary.
  add : unquote (getAgdaHighType addType)
  add = unquote (ffi-lift addType (quote add')) -- unquote (ffi-lift addType (quote add'))


module VecIso where
  open import Data.List as L
  open import Data.Nat as N
  open import Data.Maybe
  open import Data.Vec
  open import Relation.Nullary
  open import Level
  open import Contracts.Base
  open import Relation.Binary.PropositionalEquality
  open import Data.Product

  list⇒vec : ∀ {l} {n : ℕ} {A : Set l} → List A → Maybe (Vec A n)
  list⇒vec {_} {n} xs with n N.≟ L.length xs
  list⇒vec xs | yes refl = just (Data.Vec.fromList xs)
  list⇒vec xs | no ¬p = nothing

  vec⇔listI : {l : Level} → PartIso
  vec⇔listI {l} = mkPartIso L.[ Lift {_} {l} (Set l) ] L.[ (Lift ℕ) ]
      (λ x → (List (lower x)) , (λ x₁ → (Vec (lower x) (lower x₁)) , ((withMaybe list⇒vec) , (total Data.Vec.toList))))


  vec⇔list' : {l : Level} → PartIsoInt
  vec⇔list' {l} = record --toIntPartIso partIso (quote partIso) (quoteTerm partIso)
    { wrappedₙ = quote vl } --; wrapped = partIso }
    where vl = vec⇔listI {l}


module MapEx where
  open VecIso
  open NatIntIso
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Integer
  open import Data.Nat
  import Data.Vec as V
  open import Reflection

  mapImpl : (ℤ → ℤ) → L.List ℤ → L.List ℤ
  mapImpl f L.[] = L.[]
  mapImpl f (x L.∷ xs) = f x L.∷ mapImpl f xs

  -- map higher order fun, where we convert the inputs of the higher order thingie
  mapNZType : T 0
  mapNZType =
      π (
        π (iso ℕ⇔ℤ' L.[] L.[]) ∣ Keep ⇒ (iso ℕ⇔ℤ' L.[] L.[])
--        π (def (quote ℤ) ∙ []) ⇒ (def (quote ℤ) ∙ [])
        ) ∣ Keep
    ⇒ (π (def (quote L.List) ∙ [ (def (quote ℤ) ∙ []) ]) ∣ Keep
    ⇒ (def (quote L.List) ∙ [ (def (quote ℤ) ∙ []) ]))

  myMap : unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
  myMap = unquote (ffi-lift mapNZType (quote mapImpl))

module DepSimple where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin
  import Data.Vec as V
  open import Reflection

  mapImpl2 : (n : ℕ) (A : Set) → List A
  mapImpl2 n A = []

  mapNZType : T 0
  mapNZType =
    π def quote ℕ ∙ [] ∣ Keep -- n
    ⇒ (π set 0 ∣ Keep -- A
    ⇒ iso (vec⇔list' {Level.zero}) L.[ var # 0 ∙ [] ] L.[ var # 1 ∙ [] ] )

--  lowType : Set (Level.suc Level.zero)
--  lowType = {!!} --unquote (getAgdaLowType mapNZType)

--  lk : {!!}
--  lk = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}

  import Agda.Primitive
  import Data.Product

--  partIso : PartIso {Level.zero}
--  partIso = PartIsoInt.wrapped VecIso.vec⇔list

  fixType : ∀ {a} (A : Set a) → A → A
  fixType _ x = x

  import Data.Nat.Base
  import Data.List.Base
  import Data.Vec

  myMap2 : unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
--  myMap2 =  {!pretty (elimLets (ffi-lift mapNZType (quote mapImpl2)))!}
  myMap2 = unquote (ffi-lift mapNZType (quote mapImpl2)) -- unquote (ffi-lift mapNZType (quote mapImpl2))

module DepCon1 where
  open VecIso
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List as L
  open import Data.Fin
  import Data.Vec as V
  open import Reflection

  mapImpl2 : (A : Set) (B : Set) → (A → B) → List A → List B
  mapImpl2 A B = L.map

  mapNZType : T 0
  mapNZType =
    π def quote ℕ ∙ [] ∣ Discard -- n
    ⇒ (π set 0 ∣ Keep -- A
    ⇒ (π set 0 ∣ Keep -- B
    ⇒ (π (
      π var # 1 ∙ [] ∣ Keep
      ⇒ (var # 1 ∙ [])) ∣ Keep -- f
    ⇒ (π iso (vec⇔list' {Level.zero}) L.[ var # 2 ∙ [] ] L.[ var # 3 ∙ [] ] ∣ Keep -- vec
    ⇒ iso (vec⇔list' {Level.zero}) L.[ var # 2 ∙ [] ] L.[ var # 4 ∙ [] ] ))))

--  lowType : Set (Level.suc Level.zero)
--  lowType = {!!} --unquote (getAgdaLowType mapNZType)

--  lk : {!!}
--  lk = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}

  import Agda.Primitive
  import Data.Product

--  partIso : PartIso {Level.zero}
--  partIso = PartIsoInt.wrapped VecIso.vec⇔list

  fixType : ∀ {a} (A : Set a) → A → A
  fixType _ x = x

  import Data.Nat.Base


  myMap2 : unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType) --unquote (getAgdaHighType mapNZType)
--  myMap2 =  {!pretty (elimLets (ffi-lift mapNZType (quote mapImpl2)))!}
  myMap2 = unquote (ffi-lift mapNZType (quote mapImpl2)) -- unquote (ffi-lift mapNZType (quote mapImpl2))
  
    
module DepCon where
  open VecIso
  open import Data.Vec as Vec hiding ([_])
  open import Data.Nat
  open import Contracts.Base
  open import Level
  open import Data.List
  open import Data.Fin
  open import Reflection

  mapImpl2 : (n : ℕ) (A : Set) (B : Set) → (A → B) → Vec A n → Vec B n
  mapImpl2 n A B = Vec.map

--  lifth : ℕ → Lift ℕ
--  lifth = {!!}
{-
  mapNZType : T {Level.zero} 0
  mapNZType =
    π def quote ℕ ∙ [] -- n
    ⇒ (π set 0 -- A
    ⇒ (π set 0 -- B
    ⇒ (π (
      π var # 1 ∙ []
      ⇒ (var # 1 ∙ [])) -- f
    ⇒ (π iso vec⇔list [ var # 2 ∙ [] ] [ var # 3 ∙ [] ] -- vec A n
    ⇒ iso vec⇔list [ var # 2 ∙ [] ] [ var # 4 ∙ [] ] )))) -- ) vec B n

  lowType : Set (Level.suc Level.zero)
  lowType = unquote (getAgdaLowType mapNZType)

  lk : {!pretty (quoteTerm (ℕ → (A B : Set) → (f : A -> B) -> List A -> List B))!}
  lk = {!unquote (getAgdaHighType mapNZType)!}
  open import Data.Product
  open import Function

  k : ℕ → Set → Conversions {!!} {!!}
  k n A = {!!}
    where 

{-  myMap2' : unquote (getAgdaHighType mapNZType)
  myMap2' = λ n → λ A → λ f → let f' : (x : A) → A
                                  f' = λ x → f x
                               in λ xs → let xs' = unsafeConvert {!!} xs
                                            in {!!}-}

  myMap2 : unquote (getAgdaHighType mapNZType)
--  myMap2 = unquote (ffi-lift mapNZType (quote mapImpl2))
  myMap2 = {!pretty (ffi-lift mapNZType (quote mapImpl2))!}
    
-}
-- surface syntax tests
module T3 where
  open NatIntIso
  open VecIso
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

  record PartIsoPub {l} : Set (Level.suc (Level.suc l)) where
    constructor mkIsoPub
    field partIso : PartIso {l}
    field partIsoInt : PartIsoInt

  ℕ⇔ℤ : PartIsoPub
  ℕ⇔ℤ = record { partIso = ℕ⇔ℤI ; partIsoInt = ℕ⇔ℤ' }

  vec⇔list : {l : Level} → PartIsoPub {l}
  vec⇔list {l} = record { partIso = vec⇔listI ; partIsoInt = (vec⇔list' {l}) }

  getArgs : ∀ {l} → PartIsoPub {l} → Set (Level.suc l)
  getArgs p = WithArgs ((PartIso.LOWₐ h) List.++ ( PartIso.HIGHₐ h))
    where h = PartIsoPub.partIso p --PartIsoInt.wrapped p

  data AST {l m} : Set (Level.suc (Level.suc (l Level.⊔ m )))

  getTy : ∀ {l m} → AST {l} {m} → Set (l Level.⊔ m )

  data AST {l m} where
    pi : (a : AST {l} {l}) → ArgWay → (getTy a → AST {m} {m}) → AST
    ⟦_⟧ : (A : Set (l Level.⊔ m)) → AST -- normal type (List, Nat, etc..)
--    ⟦Set_⟧ : (ll : Level) → {lt : ll Level≤ l} → AST
    ⟦_⇋_⟧ : (pi :  PartIsoPub {l Level.⊔ m}) → getArgs pi → AST -- isomorphism

  split++ : ∀ {l} {a : ArgTys {l}} → {b : ArgTys {l}} → (args : WithArgs (a List.++ b)) → (WithArgs a × WithArgs b)
  split++ {a = []} args = [] , args
  split++ {a = x ∷ a} (a₁ , args) = (a₁ , (proj₁ r)) , (proj₂ r)
    where r = split++ args

  getTy (pi a _ x) = (arg : getTy a) → (getTy (x arg))
  getTy (⟦ x ⟧) = x
--  getTy {l} (⟦Set_⟧ ll {lt}) = {!!} --Lift {Level.suc ll} {l} (Set ll)
  getTy (⟦ x ⇋ x₁ ⟧) = proj₁ (applyArgs (proj₂ g) (proj₂ k)) --(PartIso.iso h) x₁
    where h = PartIsoPub.partIso x --PartIsoInt.wrapped x
          k = split++ {_} {PartIso.LOWₐ h} x₁
          g = applyArgs (PartIso.iso h) (proj₁ k)

  id : ∀ {a} {A : Set a} → A → A
  id x = x

  piK : ∀ {l m} → (a : AST {l} {l}) → (getTy a → AST {m} {m}) → AST {l} {m}
  piK x = pi x Keep
  piD : ∀ {l m} → (a : AST {l} {l}) → (getTy a → AST {m} {m}) → AST {l} {m}
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

  postulate Errrr Errrr2 Errrr3 : ∀ {a} → {A : Set a} → A

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



open import IO
import IO.Primitive
open import Data.Unit
open import Data.Nat.Show
import Data.List
open import Data.Integer
open import Data.Nat

--open MapEx
open DepCon1
open import Data.Vec

postulate exError : {A : Set} → A


main : IO.Primitive.IO ⊤
main = run (putStrLn (Data.Nat.Show.show s))
  where n = 3
        p : Vec ℤ n
        p = + 0 ∷ (-[1+ 48 ] ∷ (+ 13 ∷ []))
        kk = myMap2 n ℤ ℕ (∣_∣) p

        s = foldl (λ _ → ℕ) Data.Nat._+_ 0 kk
