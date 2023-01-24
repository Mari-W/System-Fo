open import Common using (_▷_; _▷▷_; Ctxable; ⊤ᶜ; ⊥ᶜ; r)
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

module SystemF.Target where

-- Sorts --------------------------------------------------------------------------------

data Sort : Ctxable → Set where
  eₛ  : Sort ⊤ᶜ
  σₛ  : Sort ⊤ᶜ
  vₛ  : Sort ⊥ᶜ

Sorts : Set
Sorts = List (Sort ⊤ᶜ)

variable
  s s' s'' s₁ s₂ : Sort r
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  α α' α'' α₁ α₂ : σₛ ∈ S

Var : Sorts → Sort ⊤ᶜ → Set
Var S s = s ∈ S

-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ Λ`α→_ `let`x=_`in_ ∀`α_
infixr 5 _⇒_ _·_ _•_
infix  6 `_ 

data Term : Sorts → Sort r → Set where
  `_           : Var S s → Term S s
  tt           : Term S eₛ
  λ`x→_        : Term (S ▷ eₛ) eₛ → Term S eₛ
  Λ`α→_        : Term (S ▷ σₛ) eₛ → Term S eₛ
  _·_          : Term S eₛ → Term S eₛ → Term S eₛ
  _•_          : Term S eₛ → Term S σₛ → Term S eₛ
  `let`x=_`in_ : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  `⊤           : Term S σₛ
  _⇒_          : Term S σₛ → Term S σₛ → Term S σₛ
  ∀`α_         : Term (S ▷ σₛ) σₛ → Term S σₛ

Expr : Sorts → Set
Expr S = Term S eₛ
Type : Sorts → Set
Type S = Term S σₛ

variable
  e e' e'' e₁ e₂ : Expr S
  σ σ' σ'' σ₁ σ₂ : Type S
 
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
ren ρ (Λ`α→ e) = Λ`α→ (ren (extᵣ ρ) e)
ren ρ (e₁ · e₂) = (ren ρ e₁) · (ren ρ e₂)
ren ρ (e • σ) = (ren ρ e) • (ren ρ σ)
ren ρ (`let`x= e₂ `in e₁) = `let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ `⊤ = `⊤
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (∀`α σ) = ∀`α (ren (extᵣ ρ) σ)

wk : Term S s → Term (S ▷ s') s
wk = ren there

-- Substitution -------------------------------------------------------------------------

binds : Sort r → Sort ⊤ᶜ
binds eₛ = eₛ
binds σₛ = σₛ
binds vₛ = eₛ

Sub : Sorts → Sorts → Set
Sub S₁ S₂ = ∀ {s} → Var S₁ s → Term S₂ s

extₛ : Sub S₁ S₂ → Sub (S₁ ▷ s) (S₂ ▷ s)
extₛ ξ (here refl) = ` here refl
extₛ ξ (there x) = ren wkᵣ (ξ x)

sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
sub ξ (` x) = (ξ x)
sub ξ tt = tt
sub ξ (λ`x→ e) = λ`x→ (sub (extₛ ξ) e)
sub ξ (Λ`α→ e) = Λ`α→ (sub (extₛ ξ) e)
sub ξ (e₁ · e₂) = sub ξ e₁ · sub ξ e₂
sub ξ (e • σ) = sub ξ e • sub ξ σ
sub ξ (`let`x= e₂ `in e₁) = `let`x= sub ξ e₂ `in (sub (extₛ ξ) e₁)
sub ξ `⊤ = `⊤
sub ξ (τ₁ ⇒ τ₂) = sub ξ τ₁ ⇒ sub ξ τ₂
sub ξ (∀`α σ) = ∀`α (sub (extₛ ξ) σ)

introduce :  Term S (binds s) → Sub (S ▷ (binds s)) S
introduce e (here refl) = e
introduce e (there x) = ` x 

_[_] : Term (S ▷ (binds s)) s → Term S (binds s) → Term S s
e₁ [ e₂ ] = sub (introduce e₂) e₁

variable
  ξ ξ' ξ'' ξ₁ ξ₂ : Sub S S₂ 

-- Context ------------------------------------------------------------------------------

Stores : Sorts → Sort ⊤ᶜ → Set
Stores S eₛ = Type S
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

wk-stores : Stores S s → Stores (S ▷ s') s
wk-stores {s = eₛ} σ = wk σ
wk-stores {s = σₛ} _ = tt

wk-stored : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-stored (here refl) t = wk-stores t
wk-stored (there x) t = wk-stores (wk-stored x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-stored x (lookup Γ x)

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S

-- Typing -------------------------------------------------------------------------------

-- Renaming Typing

idᵣ : Ren S S
idᵣ = id

ren' : Ren S₁ S₂ → Stores S₁ s → Stores S₂ s
ren' {s = eₛ} ρ σ = ren ρ σ
ren' {s = σₛ} ρ st = tt   

dropᵣ : Ren S₁ S₂ → Ren S₁ (S₂ ▷ s) 
dropᵣ ρ x = there (ρ x)

data OPE : Ren S₁ S₂ → Ctx S₁ → Ctx S₂ -> Set where
  ope-id : ∀ {Γ} → OPE {S₁ = S} {S₂ = S} idᵣ Γ Γ
  ope-keep : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₁ s} → 
    OPE ρ Γ₁ Γ₂ →
    --------------------------------------
    OPE (extᵣ ρ) (Γ₁ ▶ st) (Γ₂ ▶ ren' ρ st)
  ope-drop : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₂ s} →
    OPE ρ Γ₁ Γ₂ →
    -------------------------
    OPE (dropᵣ ρ) Γ₁ (Γ₂ ▶ st)

-- Expression Typing

infixr 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Expr S → Type S → Set where
  ⊢-`x :  
    wk-ctx Γ x ≡ σ →
    ----------------
    Γ ⊢ ` x ∶ σ
  ⊢-⊤ : 
    --------------
    Γ ⊢ tt ∶ `⊤
  ⊢-λ : 
    Γ ▶ σ ⊢ e ∶ wk σ →  
    ---------------------------
    Γ ⊢ λ`x→ e ∶ σ
  ⊢-Λ : 
    Γ ▶ tt ⊢ e ∶ wk σ →  
    ---------------------------
    Γ ⊢ Λ`α→ e ∶ σ
  ⊢-· : 
    Γ ⊢ e₁ ∶ σ₁ ⇒ σ₂ →
    Γ ⊢ e₂ ∶ σ₁ →
    -----------------------
    Γ ⊢ e₁ · e₂ ∶ σ₂
  ⊢-• : 
    Γ ⊢ e ∶ ∀`α σ' →
    -----------------------
    Γ ⊢ e • σ ∶ σ' [ σ ]
  ⊢-let : 
    Γ ⊢ e₂ ∶ σ →
    Γ ▶ σ ⊢ e₁ ∶ wk σ' →
    ----------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ σ'

-- Semantics ----------------------------------------------------------------------------

-- Soundness ----------------------------------------------------------------------------