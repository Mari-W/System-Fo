open import Common using (_▷_; _▷▷_; Ctxable; ⊤ᶜ; ⊥ᶜ; r)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (id; _∘_)

module SystemF where

-- Sorts --------------------------------------------------------------------------------

data Sort : Ctxable → Set where
  eₛ  : Sort ⊤ᶜ
  σₛ  : Sort ⊤ᶜ

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

idᵣ : Ren S S
idᵣ = id

wkᵣ : Ren S (S ▷ s) 
wkᵣ = there

extᵣ : Ren S₁ S₂ → Ren (S₁ ▷ s) (S₂ ▷ s)
extᵣ ρ (here refl) = here refl
extᵣ ρ (there x) = there (ρ x)

dropᵣ : Ren S₁ S₂ → Ren S₁ (S₂ ▷ s) 
dropᵣ ρ x = there (ρ x)

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

variable
  ρ ρ' ρ'' ρ₁ ρ₂ : Ren S₁ S₂

-- Substitution -------------------------------------------------------------------------

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

introduce :  Term S s → Sub (S ▷ s) S
introduce t (here refl) = t
introduce t (there x) = ` x
_[_] : Term (S ▷ s') s → Term S s' → Term S s
t [ t' ] = sub (introduce t') t

variable
  ξ ξ' ξ'' ξ₁ ξ₂ : Sub S₁ S₂ 

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

Types : Sorts → Sort ⊤ᶜ → Set
Types S eₛ = Type S
Types S σₛ = ⊤

↑ₜ : Stores S s → Types S s
↑ₜ {s = eₛ} σ = σ
↑ₜ {s = σₛ} _ = tt

variable 
  T T' T'' T₁ T₂ : Types S s

-- Expression Typing

infix 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Term S s → Types S s → Set where
  ⊢`x :  
    wk-ctx Γ x ≡ σ →
    ----------------
    Γ ⊢ ` x ∶ σ
  ⊢⊤ : 
    --------------
    Γ ⊢ tt ∶ `⊤
  ⊢λ : 
    Γ ▶ σ ⊢ e ∶ wk σ' →  
    ---------------------------
    Γ ⊢ λ`x→ e ∶ σ ⇒ σ' 
  ⊢Λ : 
    Γ ▶ tt ⊢ e ∶ σ →  
    ---------------------------
    Γ ⊢ Λ`α→ e ∶ ∀`α σ
  ⊢· : 
    Γ ⊢ e₁ ∶ σ₁ ⇒ σ₂ →
    Γ ⊢ e₂ ∶ σ₁ →
    -----------------------
    Γ ⊢ e₁ · e₂ ∶ σ₂
  ⊢• : 
    Γ ⊢ e ∶ ∀`α σ' →
    -----------------------
    Γ ⊢ e • σ ∶ σ' [ σ ]
  ⊢let : 
    Γ ⊢ e₂ ∶ σ →
    Γ ▶ σ ⊢ e₁ ∶ wk σ' →
    ----------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ σ'
  ⊢σ :
    ----------
    Γ ⊢ σ ∶ tt

-- Renaming Typing

ren' : Ren S₁ S₂ → Stores S₁ s → Stores S₂ s
ren' {s = eₛ} ρ σ = ren ρ σ
ren' {s = σₛ} ρ _ = tt   

infix 3 _∶_⇒ᵣ_
data _∶_⇒ᵣ_ : Ren S₁ S₂ → Ctx S₁ → Ctx S₂ → Set where
  ⊢idᵣ : ∀ {Γ} → _∶_⇒ᵣ_ {S₁ = S} {S₂ = S} idᵣ Γ Γ
  ⊢keepᵣ : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₁ s} → 
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    --------------------------------------
    (extᵣ ρ) ∶ (Γ₁ ▶ st) ⇒ᵣ (Γ₂ ▶ ren' ρ st)
  ⊢dropᵣ : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₂ s} →
    ρ ∶ Γ₁  ⇒ᵣ Γ₂ →
    -------------------------
    (dropᵣ ρ) ∶ Γ₁ ⇒ᵣ (Γ₂ ▶ st)

-- Substitution Typing

sub' : Sub S₁ S₂ → Stores S₁ s → Stores S₂ s
sub' {s = eₛ} ρ σ = sub ρ σ
sub' {s = σₛ} ρ st = tt   
 
_∶_⇒ₛ_ : Sub S₁ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_⇒ₛ_ {S₁ = S₁} ξ Γ₁ Γ₂ = ∀ {s} → (x : Var S₁ s) → Γ₂ ⊢ ξ x ∶ ↑ₜ (sub' ξ (wk-ctx Γ₁ x))
 
-- Semantics ----------------------------------------------------------------------------

-- call by value --
data Val : Expr S → Set where
  v-λ : Val (λ`x→ e)
  v-Λ : Val (Λ`α→ e)
  v-tt : ∀ {S} → Val (tt {S = S})
  
infixr 3 _↪_
data _↪_ : Expr S → Expr S → Set where
  β-λ :
    Val e₂ →
    ---------------------------------
    (λ`x→ e₁) · e₂ ↪ (e₁ [ e₂ ])
  β-Λ :
    ----------------------
    (Λ`α→ e) • σ ↪ e [ σ ]
  β-let : 
     Val e₂ →
     ------------------------------------
    `let`x= e₂ `in e₁ ↪ (e₁ [ e₂ ])
  ξ-·₁ :
    e₁ ↪ e →
    ----------------
    e₁ · e₂ ↪ e · e₂
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    ----------------------
    e₁ · e₂ ↪ e₁ · e
  ξ-• :
    e ↪ e' →
    ----------------
    e • σ ↪ e' • σ
  ξ-let :
    e₂ ↪ e →
    ------------------------------------
    `let`x= e₂ `in e₁ ↪ `let`x= e `in e₁ 

-- Soundness ---------------------------------------------------------------------------- 

-- Progress

progress : 
  ∅ ⊢ e ∶ σ →
  (∃[ e' ] (e ↪ e')) ⊎ Val e
progress ⊢⊤ = inj₂ v-tt
progress (⊢λ _) = inj₂ v-λ
progress (⊢Λ _) = inj₂ v-Λ
progress (⊢· {e₁ = e₁} {e₂ = e₂} ⊢e₁  ⊢e₂) with progress ⊢e₁ | progress ⊢e₂ 
... | inj₁ (e₁' , e₁↪e₁') | _ = inj₁ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
... | inj₂ v | inj₁ (e₂' , e₂↪e₂') = inj₁ (e₁ · e₂' , ξ-·₂ e₂↪e₂' v)
... | inj₂ (v-λ {e = e₁}) | inj₂ v = inj₁ (sub (introduce e₂) e₁ , β-λ v)
progress (⊢• {σ = σ} ⊢e) with progress ⊢e 
... | inj₁ (e' , e↪e') = inj₁ (e' • σ , ξ-• e↪e')
... | inj₂ (v-Λ {e = e}) = inj₁ (sub (introduce σ) e , β-Λ)
progress (⊢let  {e₂ = e₂} {e₁ = e₁} ⊢e₂ ⊢e₁) with progress ⊢e₂ 
... | inj₁ (e₂' , e₂↪e₂') = inj₁ ((`let`x= e₂' `in e₁) , ξ-let e₂↪e₂')
... | inj₂ v = inj₁ (sub (introduce e₂) e₁ , β-let v)

-- Subject Reduction

{- ren-preserves : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {σ : Type S₁} →
  ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
  Γ₁ ⊢ e ∶ σ →
  Γ₂ ⊢ (ren ρ e) ∶ (ren ρ σ)
ren-preserves ⊢ (⊢-`x refl) = ⊢-`x {!   !}
ren-preserves ⊢ρ ⊢-⊤ = ⊢-⊤
ren-preserves ⊢ρ (⊢-λ ⊢e) = ⊢-λ {! ren-preserves ? ?  !}
ren-preserves ⊢ρ (⊢-Λ ⊢e) = ⊢-Λ (ren-preserves (ope-keep ⊢ρ) ⊢e)
ren-preserves ⊢ρ (⊢-· ⊢e₁ ⊢e₂) = ⊢-· (ren-preserves ⊢ρ ⊢e₁) (ren-preserves ⊢ρ ⊢e₂)
ren-preserves ⊢ρ (⊢-• ⊢e) = {!   !}
ren-preserves ⊢ρ (⊢-let ⊢e₂ ⊢e₁) = ⊢-let (ren-preserves ⊢ρ ⊢e₂) {!  (ren-preserves (ope-keep ⊢ρ) ⊢e₁) !}

sub-preserves : ξ ∶ Γ₁ ⇒ₛ Γ₂ →
  Γ₁ ⊢ e ∶ σ →
  Γ₂ ⊢ (sub ξ e) ∶ (sub ξ σ)
sub-preserves ξ ⊢e = {!   !}

subject-reduction : ∀ {Γ : Ctx S} →
  Γ ⊢ e ∶ σ →
  e ↪ e' →
  Γ ⊢ e' ∶ σ
subject-reduction a r = {!   !}
 -} 