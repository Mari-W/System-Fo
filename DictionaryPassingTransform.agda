open import HindleyMilner renaming (_⊢_ to _⊢ₕ_; _⊢_∶_ to _⊢ₕ_∶_; Val to Valₕ; Ctx to Ctxₕ; [Mode] to [Mode]ₕ; Mode to Modeₕ; eₘ to eₘₕ; σₘ to σₘₕ)
open import SystemO renaming (_⊢_ to _⊢ₒ_; _⊢_∶_ to _⊢ₒ_∶_; Val to Valₒ; Ctx to Ctxₒ; [Mode] to [Mode]ₒ; Mode to Modeₒ; eₘ to eₘₒ; σₘ to σₘₒ)

module DictionaryPassingTransform where

variable
  μₒ  : [Mode]ₒ
  eₒ  : μₒ ⊢ₒ eₘₒ
  σₒ  : μₒ ⊢ₒ σₘₒ
  Γₒ  : Ctxₒ μₒ

  μₕ  : [Mode]ₕ
  eₕ  : μₕ ⊢ₕ eₘₕ
  σₕ  : μₕ ⊢ₕ σₘₕ
  Γₕ  : Ctxₕ μₕ

infixr 3 _⊢_∶_≻_
data _⊢_∶_≻_ : Ctxₒ μₒ → μₒ ⊢ₒ eₘₒ → μₒ ⊢ₒ σₘₒ → μₕ ⊢ₕ eₘₕ → Set where
  
→σₕ_ : 
  μₒ ⊢ₒ σₘₒ → 
  μₕ ⊢ₕ σₘₕ
→σₕ a = {!   !}  

→Γₕ_ :
  Ctxₒ μₒ → 
  Ctxₕ μₕ
→Γₕ Γ = {!   !}

→ₕ_ :
  Γₒ ⊢ eₒ ∶ σₒ ≻ eₕ →
  (→Γₕ Γₒ) ⊢ₕ eₕ ∶ {! →σₕ σₒ !}
→ₕ e = {!    !}