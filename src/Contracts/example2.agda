{-# OPTIONS --type-in-type #-}
module Contracts.example2 where


module EvenWitness where
  open import Data.Nat
  open import Contracts.SSyn
  open import Contracts.Witness

  postulate hsAdd : ℕ → ℕ → ℕ
  
  data Even : ℕ → Set where
    Z : Even 0
    SS : {n : ℕ} → Even n → Even (suc (suc n))
  

  open import Relation.Nullary
  even? : (n : ℕ) → Dec (Even n)
  even? zero = yes Z
  even? (suc zero) = no (λ { () })
  even? (suc (suc n)) with even? n
  even? (suc (suc n)) | yes p = yes (SS p)
  even? (suc (suc n)) | no ¬p = no (λ { (SS x) → ¬p x } )

  open import Data.Product
  open import Data.Unit
  add : Σ ℕ Even → Σ ℕ Even → Σ ℕ Even
  add = assert (makeContract (
    ⟨ _ ∷ ⟦ ⇔Witness ⇋ evenDec ⟧ ⟩⇒
    ⟨ _ ∷ ⟦ ⇔Witness ⇋ evenDec ⟧ ⟩⇒
    ⟨     ⟦ ⇔Witness ⇋ evenDec ⟧ ⟩)) hsAdd
    where
      evenDec = (ℕ , Even , even?) , wrap tt , wrap tt


module Gcd where
  open import Data.Nat
  open import Contracts.SSyn
  open import Contracts.Witness
  open import Data.Product
  open import Data.Unit

  data _Divides_ : ℕ → ℕ → Set where
  infixr 10 _Divides_


  open import Relation.Nullary
  postulate _divides?_ : (x : ℕ) → (y : ℕ) → Dec (x Divides y)

  dec-× : ∀ {A B C} → (A → Dec B) → (A → Dec C) → A → Dec (B × C)
  dec-× b c a with b a | c a
  dec-× b c a | yes p | yes p₁ = yes (p , p₁)
  dec-× b c a | yes p | no ¬p = no (λ x → ¬p (proj₂ x))
  dec-× b c a | no ¬p | c' = no (λ x → ¬p (proj₁ x))

  postulate hsGcd : ℕ → ℕ → ℕ

  gcd : (x y : ℕ) → Σ ℕ (λ z → (z Divides x × z Divides y))
  gcd = assert (makeContract (
    ⟨ x ∷ ⟦ ℕ ⟧ ⟩⇒
    ⟨ y ∷ ⟦ ℕ ⟧ ⟩⇒
    ⟨ ⟦ ⇔Witness ⇋ (ℕ , ((λ z → z Divides x × z Divides y) , (λ z → dec-× (λ _ → z divides? x) (λ _ → z divides? y) z))) , wrap tt , wrap tt ⟧ ⟩
    )) hsGcd
