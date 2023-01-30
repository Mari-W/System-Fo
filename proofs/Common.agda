open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Common where

infix 25 _▷_ _▷▷_
pattern _▷_ xs x = x ∷ xs
_▷▷_ : {A : Set} → List A → List A → List A
xs ▷▷ ys = ys ++ xs

data Ctxable : Set where
  ⊤ᶜ : Ctxable
  ⊥ᶜ : Ctxable

variable
  r r' r'' r₁ r₂ : Ctxable

{- _≡ᶠ_ : {A : Set} {B : A → Set} {C : (a : A) → B a → Set} (f g : ∀ {a : A} → (b : B a) → C a b) → Set
_≡ᶠ_ {B = B} f g = ∀ {a} (b : B a) → f b ≡ g b -}