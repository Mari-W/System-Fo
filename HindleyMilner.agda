{-# OPTIONS --allow-unsolved-metas #-}

open import Data.List using (List; []; _∷_; drop; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Nullary using (¬_)

module HindleyMilner where

-- Preliminary --------------------------------------------------------------------------

infix 25 _▷_ _▷▷_
pattern _▷_ xs x = x ∷ xs
_▷▷_ : {A : Set} → List A → List A → List A
xs ▷▷ ys = ys ++ xs

-- Sorts --------------------------------------------------------------------------------

data Refable : Set where
  ⊤ᵣ : Refable
  ⊥ᵣ : Refable

data Sort : Refable → Set where
  eₛ  : Sort ⊤ᵣ 
  σₛ  : Sort ⊥ᵣ
  τₛ  : Sort ⊤ᵣ

Sorts : Set
Sorts = List (Sort ⊤ᵣ)

variable
  r r' r'' r₁ r₂ : Refable
  s s' s'' s₁ s₂ : Sort r
  S S' S'' S₁ S₂ : Sorts
  a a' a'' a₁ a₂ : s ∈ S
  x x' x'' x₁ x₂ : eₛ ∈ S
  α α' α'' α₁ α₂ : τₛ ∈ S


Var : Sorts → Sort ⊤ᵣ → Set
Var S s = s ∈ S

-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ `let`x=_`in_ ∀`α_
infixr 5 _⇒_ _·_
infix  6 `_ ↑ₚ_

data Term : Sorts → Sort r → Set where
  `_           : Var S s → Term S s
  λ`x→_        : Term (S ▷ eₛ) eₛ → Term S eₛ
  _·_          : Term S eₛ → Term S eₛ → Term S eₛ
  `let`x=_`in_ : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  _⇒_          : Term S τₛ → Term S τₛ → Term S τₛ
  ∀`α_         : Term (S ▷ τₛ) σₛ → Term S σₛ
  ↑ₚ_          : Term S τₛ → Term S σₛ

Expr : Sorts → Set
Expr S = Term S eₛ
Poly : Sorts → Set
Poly S = Term S σₛ
Mono : Sorts → Set
Mono S = Term S τₛ

variable
  e e' e'' e₁ e₂ : Expr S
  σ σ' σ'' σ₁ σ₂ : Poly S
  τ τ' τ'' τ₁ τ₂ : Mono S

data Val : Expr S → Set where
  val-λ : Val (λ`x→ e)

variable
  v v' v'' v₁ v₂ : Val e 

-- Context ------------------------------------------------------------------------------

Stores : Sorts → Sort ⊤ᵣ → Set
Stores S eₛ = Mono S
Stores S τₛ = ⊤

depth : Var S s → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

drop-last : ∀ {S s} → Var S s → Sorts → Sorts
drop-last = drop ∘ suc ∘ depth

Ctx : Sorts → Set
Ctx S = ∀ {s} → (v : Var S s) → Stores (drop-last v S) s

infix 30 _▶_
_▶_ : Ctx S → Stores S s → Ctx (S ▷ s)
(Γ ▶ γ) (here refl) = γ
(Γ ▶ _) (there x) = Γ x

wk-τ : Mono S → Term (S ▷ s') τₛ 
wk-τ (` x) = ` there x
wk-τ (τ₁ ⇒ τ₂) = (wk-τ τ₁ ⇒ wk-τ τ₂) 

wk-σ : Poly S → Term (S ▷ s') σₛ
wk-σ (∀`α σ) = ∀`α {! TODO EXT-WK !}
wk-σ (↑ₚ τ) = ↑ₚ (wk-τ τ)

wk-t : ∀ {s} → Stores S s → Stores (S ▷ s') s
wk-t {s = eₛ} τ = wk-τ τ
wk-t {s = τₛ} _ = tt  

wk-drop : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-drop (here refl) t = wk-t t
wk-drop (there x) t = wk-t (wk-drop x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-drop x (Γ x)

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S
  ∅ : Ctx []

-- Renaming -----------------------------------------------------------------------------

Ren : Sorts → Sorts → Set
Ren S₁ S₂ = ∀ {s} → Var S₁ s → Var S₂ s

extᵣ : Ren S₁ S₂ → Ren (S₁ ▷ s) (S₂ ▷ s)
extᵣ ρ (here refl) = here refl
extᵣ ρ (there x) = there (ρ x)

ren : Ren S₁ S₂ → (Term S₁ s → Term S₂ s)
ren ρ (` x) = ` (ρ x)
ren ρ (λ`x→ e) = λ`x→ (ren (extᵣ ρ) e)
ren ρ (e₁ · e₂) = (ren ρ e₁) · (ren ρ e₂)
ren ρ (`let`x= e₂ `in e₁) = `let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (↑ₚ τ) = ↑ₚ ren ρ τ
ren ρ (∀`α σ) = ∀`α (ren (extᵣ ρ) σ)

wkᵣ : Ren S (S ▷ s) 
wkᵣ = there

-- Substitution -------------------------------------------------------------------------

takes : Sort r → Sort ⊤ᵣ 
takes eₛ = eₛ
takes σₛ = τₛ
takes τₛ = τₛ

Sub : Sorts → Sorts → Set
Sub S₁ S₂ = ∀ {s} → Var S₁ s → Term S₂ s

extₛ : Sub S₁ S₂ → Sub (S₁ ▷ s) (S₂ ▷ s)
extₛ ξ (here refl) = ` here refl
extₛ ξ (there x) = ren wkᵣ (ξ x)

sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
sub ξ (` x) = (ξ x)
sub ξ (λ`x→ e) = λ`x→ (sub (extₛ ξ) e)
sub ξ (e₁ · e₂) = sub ξ e₁ · sub ξ e₂
sub ξ (`let`x= e₂ `in e₁) = `let`x= sub ξ e₂ `in (sub (extₛ ξ) e₁)
sub ξ (τ₁ ⇒ τ₂) = sub ξ τ₁ ⇒ sub ξ τ₂
sub ξ (∀`α σ) = ∀`α (sub (extₛ ξ) σ)
sub ξ (↑ₚ τ) = ↑ₚ sub ξ τ

intro : Term S (takes s) → Sub (S ▷ (takes s)) S
intro e (here refl) = e
intro e (there x) = ` x 

_[_] : Term (S ▷ (takes s)) s → Term S (takes s) → Term S s
e₁ [ e₂ ] = sub (intro e₂) e₁

variable
  ξ ξ' ξ'' ξ₁ ξ₂ : Sub S S₂ 

-- Typing -------------------------------------------------------------------------------

infixr 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Expr S → Poly S → Set where
  ⊢-` :  
    wk-ctx Γ x ≡ τ →
    ----------------
    Γ ⊢ ` x ∶ ↑ₚ τ
  ⊢-λ : 
    Γ ▶ τ₁ ⊢ e ∶ ↑ₚ (wk-τ τ₂) →  
    ---------------------------
    Γ ⊢ λ`x→ e ∶ ↑ₚ (τ₁ ⇒ τ₂)
  ⊢-· : 
    Γ ⊢ e₁ ∶ ↑ₚ (τ₁ ⇒ τ₂) →
    Γ ⊢ e₂ ∶ ↑ₚ τ₁ →
    -----------------------
    Γ ⊢ e₁ · e₂ ∶ ↑ₚ τ₂
  ⊢-let : 
    Γ ⊢ e₂ ∶ σ →
    Γ ▶ τ ⊢ e₁ ∶ ↑ₚ (wk-τ τ) →
    ----------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ ↑ₚ τ
  ⊢-τ : 
    Γ ⊢ e ∶ ∀`α σ →
    --------------------
    Γ ⊢ e ∶ (σ [ τ ])
  ⊢-∀ : 
    Γ ⊢ e ∶ σ → 
    ------------------
    Γ ⊢ e ∶ ∀`α wk-σ σ 

-- Semantics ----------------------------------------------------------------------------

infixr 3 _↪_
data _↪_ : Expr S → Expr S → Set where
  β-λ :
    Val e₂ →
    --------------------------
    (λ`x→ e₁) · e₂ ↪ e₁ [ e₂ ]
  β-let : 
    Val e₂ → 
    -----------------------------
    `let`x= e₂ `in e₁ ↪ e₁ [ e₂ ]
  {- ξ-λ :
    e ↪ e' →
    ----------------
    λ`x→ e ↪ λ`x→ e' -}
  ξ-·₁ :
    e₁ ↪ e₂ →
    ---------------
    e₁ · e ↪ e₂ · e
  ξ-·₂ :
    Val e → 
    e₁ ↪ e₂ →
    ---------------
    e · e₁ ↪ e · e₂
  ξ-let :
    e₁ ↪ e₂ →
    -----------------------------------
    `let`x= e₁ `in e ↪ `let`x= e₂ `in e

-- Progress -----------------------------------------------------------------------------

progress :
  ∅ ⊢ e ∶ σ →
  --------------------------
  (∃[ e' ] (e ↪ e')) ⊎ Val e
progress (⊢-λ _) = inj₂ val-λ
progress (⊢-· ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂ 
... | inj₁ (_ , e↪e') | _ = inj₁ (_ , ξ-·₁ e↪e')
... | inj₂ val-λ | inj₁ (_ , e↪e') = inj₁ (_ , ξ-·₂ val-λ e↪e')
... | inj₂ val-λ | inj₂ val-λ = inj₁ (_ , β-λ val-λ)
progress (⊢-let ⊢e₂ _) with progress ⊢e₂
... | inj₁ (_ , e↪e') = inj₁ (_ , ξ-let e↪e')
... | inj₂ val-λ = inj₁ (_ , β-let val-λ)
progress (⊢-τ ⊢e) = progress ⊢e
progress (⊢-∀ ⊢e) = progress ⊢e

-- Preservation -------------------------------------------------------------------------

{- preservation : 
  ∅ ⊢ e ∶ σ → 
  e ↪ e' → 
  -----------
  ∅ ⊢ e' ∶ σ
preservation (⊢-· fun arg) (β-λ v) = {!   !}
preservation (⊢-· fun arg) (ξ-·₁ red) = {!   !}
preservation (⊢-· fun arg) (ξ-·₂ v red) = {!   !}
preservation (⊢-let arg bdy) (β-let v) = {!   !}
preservation (⊢-let arg bdy) (ξ-let red) = {!   !}
preservation (⊢-τ a) b = {!   !}
preservation (⊢-∀ a) b = {!   !} -}     