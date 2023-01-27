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

cong₃ : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}{D : Set l}{a a' : A}{b b' : B}{c c' : C}
  → (f : A → B → C → D)
  → a ≡ a' 
  → b ≡ b'
  → c ≡ c'
  → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl