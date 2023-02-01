\begin{code}[hide]
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
\end{code} 