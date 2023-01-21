open import Common using (_▷_; _▷▷_)
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

module HindleyMilner.Target where

-- Sorts --------------------------------------------------------------------------------

data Sort : Set where
  eₛ  : Sort
  τₛ  : Sort
  σₛ  : Sort 

Sorts : Set
Sorts = List Sort

variable
  s s' s'' s₁ s₂ : Sort
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  α α' α'' α₁ α₂ : σₛ ∈ S

Var : Sorts → Sort → Set
Var S s = s ∈ S

-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ `let`x=_`in_ ∀`α_
infixr 5 _⇒_ _·_ 
infix  6 `_ 

data Term : Sorts → Sort → Set where
  `_           : Var S s → Term S s
  tt           : Term S eₛ
  λ`x→_        : Term (S ▷ eₛ) eₛ → Term S eₛ
  _·_          : Term S eₛ → Term S eₛ → Term S eₛ
  `let`x=_`in_ : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  `⊤           : Term S τₛ
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
  τ τ' τ'' τ₁ τ₂ : Mono S
  σ σ' σ'' σ₁ σ₂ : Poly S
 
-- Renaming -----------------------------------------------------------------------------

Ren : Sorts → Sorts → Set
Ren S₁ S₂ = ∀ {s} → Var S₁ s → Var S₂ s

extᵣ : Ren S₁ S₂ → Ren (S₁ ▷ s) (S₂ ▷ s)
extᵣ ρ (here refl) = here refl
extᵣ ρ (there x) = there (ρ x)

wkᵣ : Ren S (S ▷ s) 
wkᵣ = there

ren : Ren S₁ S₂ → (Term S₁ s → Term S₂ s)
ren ρ (` x) = ` (ρ x)
ren ρ tt = tt
ren ρ (λ`x→ e) = λ`x→ (ren (extᵣ ρ) e)
ren ρ (e₁ · e₂) = (ren ρ e₁) · (ren ρ e₂)
ren ρ (`let`x= e₂ `in e₁) = `let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ `⊤ = `⊤
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (↑ₚ τ) = ↑ₚ ren ρ τ
ren ρ (∀`α σ) = ∀`α (ren (extᵣ ρ) σ)

wk : Term S s → Term (S ▷ s') s
wk = ren there

-- Substitution -------------------------------------------------------------------------

binds : Sort → Sort 
binds eₛ = eₛ
binds τₛ = τₛ
binds σₛ = τₛ

Sub : Sorts → Sorts → Set
Sub S₁ S₂ = ∀ {s} → Var S₁ s → Term S₂ s

extₛ : Sub S₁ S₂ → Sub (S₁ ▷ s) (S₂ ▷ s)
extₛ ξ (here refl) = ` here refl
extₛ ξ (there x) = ren wkᵣ (ξ x)

sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
sub ξ (` x) = (ξ x)
sub ξ tt = tt
sub ξ (λ`x→ e) = λ`x→ (sub (extₛ ξ) e)
sub ξ (e₁ · e₂) = sub ξ e₁ · sub ξ e₂
sub ξ (`let`x= e₂ `in e₁) = `let`x= sub ξ e₂ `in (sub (extₛ ξ) e₁)
sub ξ `⊤ = `⊤
sub ξ (τ₁ ⇒ τ₂) = sub ξ τ₁ ⇒ sub ξ τ₂
sub ξ (∀`α σ) = ∀`α (sub (extₛ ξ) σ)
sub ξ (↑ₚ τ) = ↑ₚ sub ξ τ

intro :  Term S (binds s) → Sub (S ▷ (binds s)) S
intro e (here refl) = e
intro e (there x) = ` x 

_[_] : Term (S ▷ (binds s)) s → Term S (binds s) → Term S s
e₁ [ e₂ ] = sub (intro e₂) e₁

variable
  ξ ξ' ξ'' ξ₁ ξ₂ : Sub S S₂ 

-- Context ------------------------------------------------------------------------------

Stores : Sorts → Sort → Set
Stores S eₛ = Poly S
Stores S τₛ = ⊤
Stores S σₛ = ⊤

data Ctx : Sorts → Set where
  ∅   : Ctx []
  _▶_ : Ctx S → Stores S s → Ctx (S ▷ s)

depth : Var S s → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

drop-last : ∀ {S s} → Var S s → Sorts → Sorts
drop-last = drop ∘ suc ∘ depth

lookup : Ctx S → (v : Var S s) → Stores (drop-last v S) s 
lookup (Γ ▶ x) (here refl) = x
lookup (Γ ▶ x) (there t) = lookup Γ t

wk-item : Stores S s → Stores (S ▷ s') s
wk-item {s = eₛ} σ = wk σ
wk-item {s = τₛ} _ = tt
wk-item {s = σₛ} _ = tt

wk-stored : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-stored (here refl) t = wk-item t
wk-stored (there x) t = wk-item (wk-stored x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-stored x (lookup Γ x)

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S
  
-- Typing -------------------------------------------------------------------------------

infixr 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Expr S → Poly S → Set where
  ⊢-`x :  
    wk-ctx Γ x ≡ σ →
    ----------------
    Γ ⊢ ` x ∶ σ
  ⊢-⊤ : 
    --------------
    Γ ⊢ tt ∶ ↑ₚ `⊤
  ⊢-λ : 
    Γ ▶ (↑ₚ τ₁) ⊢ e ∶ ↑ₚ (wk τ₂) →  
    ---------------------------
    Γ ⊢ λ`x→ e ∶ ↑ₚ (τ₁ ⇒ τ₂)
  ⊢-· : 
    Γ ⊢ e₁ ∶ ↑ₚ (τ₁ ⇒ τ₂) →
    Γ ⊢ e₂ ∶ ↑ₚ τ₁ →
    -----------------------
    Γ ⊢ e₁ · e₂ ∶ ↑ₚ τ₂
  ⊢-let : 
    Γ ⊢ e₂ ∶ σ →
    Γ ▶ σ ⊢ e₁ ∶ ↑ₚ (wk τ) →
    ----------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ ↑ₚ τ
  ⊢-τ : 
    Γ ⊢ e ∶ ∀`α σ →
    --------------------
    Γ ⊢ e ∶ (σ [ τ ])
  ⊢-∀ : 
    Γ ⊢ e ∶ σ → 
    ------------------
    Γ ⊢ e ∶ ∀`α wk σ 

