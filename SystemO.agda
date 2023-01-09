{-# OPTIONS --allow-unsolved-metas #-}

open import Data.List using (List; []; _∷_; drop; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)

module SystemO where

-- Preliminary --------------------------------------------------------------------------

infix 25 _▷_ _▷▷_
pattern _▷_ xs x = x ∷ xs
_▷▷_ : {A : Set} → List A → List A → List A
xs ▷▷ ys = ys ++ xs

-- Sorts --------------------------------------------------------------------------------

data Ctxable : Set where
  ⊤ᵣ : Ctxable
  ⊥ᵣ : Ctxable

data Sort : Ctxable → Set where
  eₛ  : Sort ⊤ᵣ
  vₛ  : Sort ⊥ᵣ 
  oₛ  : Sort ⊤ᵣ 
  cₛ  : Sort ⊥ᵣ
  σₛ  : Sort ⊥ᵣ 
  τₛ  : Sort ⊤ᵣ

Sorts : Set
Sorts = List (Sort ⊤ᵣ)

variable
  r r' r'' r₁ r₂ : Ctxable
  s s' s'' s₁ s₂ : Sort r 
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  o o' o'' o₁ o₂ : oₛ ∈ S
  α α' α'' α₁ α₂ : τₛ ∈ S

Var : Sorts → Sort ⊤ᵣ → Set
Var S s = s ∈ S

OVar : Sorts → Set
OVar S = oₛ ∈ S
  
-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ `let`x=_`in_ ∀`α_⇒_ inst`_∶_`=_`in_ _,_
infixr 5 _⇒_ _·_ _∶_
infix  6 `_ ↑ₚ_

data Term : Sorts → Sort r → Set where
  `_              : Var S s → Term S s
  λ`x→_           : Term (S ▷ eₛ) eₛ → Term S eₛ
  _·_             : Term S eₛ → Term S eₛ → Term S eₛ
  `let`x=_`in_    : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  inst`_∶_`=_`in_ : Term S oₛ → Term S σₛ → Term S eₛ → Term S eₛ → Term S eₛ
  decl`o`in_      : Term (S ▷ oₛ) eₛ → Term S eₛ
  -λ`x→_          : Term (S ▷ eₛ) eₛ → Term S vₛ
  -_∶_            : Term S eₛ → Term S τₛ → Term S vₛ
  -_,_            : Term S vₛ → Term S vₛ → Term S vₛ
  _⇒_             : Term S τₛ → Term S τₛ → Term S τₛ
  _∶_             : Term S oₛ → Term S τₛ → Term S cₛ
  _,_             : Term S cₛ → Term S cₛ → Term S cₛ
  ∀`α_⇒_          : Term S cₛ → Term (S ▷ τₛ) σₛ → Term S σₛ
  ↑ₚ_             : Term S τₛ → Term S σₛ

Expr : Sorts → Set
Expr S = Term S eₛ
Over : Sorts → Set
Over S = Term S oₛ
Cstr : Sorts → Set
Cstr S = Term S cₛ
Poly : Sorts → Set
Poly S =  Term S σₛ
Mono : Sorts → Set
Mono S = Term S τₛ
Val : Sorts → Set
Val S = Term S vₛ

{- ⌞_⌟ : Val S → Expr S
⌞ -λ`x→ e ⌟ = λ`x→ e
-}


variable
  e e' e'' e₁ e₂ : Expr S
  v v' v'' v₁ v₂ : Val S
  c c' c'' c₁ c₂ : Cstr S
  σ σ' σ'' σ₁ σ₂ : Poly S
  τ τ' τ'' τ₁ τ₂ : Mono S

-- Context ------------------------------------------------------------------------------

variable 
  Σ Σ' Σ'' Σ₁ Σ₂ : List (Poly S)

∅ᶜ : List (Poly S)
∅ᶜ = []

Stores : Sorts → Sort ⊤ᵣ → Set
Stores S eₛ = Mono S
Stores S oₛ = List (Poly S)
Stores S τₛ = ⊤

depth : ∀ {S s} → Var S s → ℕ
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

wk-c : Cstr S → Term (S ▷ s') cₛ
wk-c (` x ∶ τ) = (` there x) ∶ wk-τ τ
wk-c (c₁ , c₂) = wk-c c₁ , wk-c c₂

wk-σ : Poly S → Term (S ▷ s') σₛ
wk-σ (∀`α c ⇒ σ) = ∀`α wk-c c ⇒ {!  TODO EXT-WK  !}
wk-σ (↑ₚ τ) = ↑ₚ (wk-τ τ)

wkₛ : Stores S s → Stores (S ▷ s') s
wkₛ {s = eₛ} τ = wk-τ τ
wkₛ {s = oₛ} [] = []
wkₛ {s = oₛ} (Σ ▷ σ) = wkₛ Σ ▷ wk-σ σ
wkₛ {s = τₛ} _ = tt  

wk-drop : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-drop (here refl) t = wkₛ t
wk-drop (there x) t = wkₛ (wk-drop x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-drop x (Γ x)

_[_]⊎_ : Ctx S → (v : Var S oₛ) → Poly (drop-last v S) → Ctx S
(Γ [ here refl ]⊎ σ) (here refl) = Γ (here refl) ▷ σ
(Γ [ there o ]⊎ σ) (here refl) = Γ (here refl)
(Γ [ _ ]⊎ σ) (there x) = Γ (there x) 

infix 30 _▶ᶜ_
_▶ᶜ_ : Ctx S → Cstr S → Ctx S
Γ ▶ᶜ (` o ∶ τ) = Γ [ o ]⊎ {! ?  !}
Γ ▶ᶜ (c , c') = (Γ ▶ᶜ c) ▶ᶜ c'

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
ren ρ (inst` o ∶ σ `= e₂ `in e₁) = inst` (ren ρ o) ∶ ren ρ σ `=  (ren ρ e₂) `in ren ρ e₁
ren ρ (decl`o`in e) = decl`o`in ren (extᵣ ρ) e
ren ρ (-λ`x→ e) = -λ`x→ (ren (extᵣ ρ) e) 
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (o ∶ σ) = ren ρ o ∶ ren ρ σ
ren ρ (c₁ , c₂) = (ren ρ c₁ , ren ρ c₂)
ren ρ (↑ₚ τ) = ↑ₚ ren ρ τ
ren ρ (∀`α cs ⇒ σ) = ∀`α ren ρ cs ⇒ ren (extᵣ ρ) σ

wkᵣ : Ren S (S ▷ s) 
wkᵣ = there

-- Substitution -------------------------------------------------------------------------

takes : Sort r → Sort ⊤ᵣ 
takes eₛ = eₛ
takes σₛ = τₛ
takes τₛ = τₛ 
takes oₛ = eₛ -- never substituted into
takes cₛ = τₛ 
takes vₛ = eₛ -- never substituted into

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
sub ξ (inst` o ∶ σ `= e₂ `in e₁) = inst` sub ξ o ∶ sub ξ σ `= sub ξ e₂ `in sub ξ e₁
sub ξ (decl`o`in e) = decl`o`in sub (extₛ ξ) e
sub ξ (-λ`x→ e) = -λ`x→ (sub (extₛ ξ) e) 
sub ξ (τ₁ ⇒ τ₂) = sub ξ τ₁ ⇒ sub ξ τ₂
sub ξ (o ∶ σ) = sub ξ o ∶ sub ξ σ
sub ξ (c₁ , c₂) = sub ξ c₁ , sub ξ c₂
sub ξ (∀`α cs ⇒ σ) = ∀`α sub ξ cs ⇒ (sub (extₛ ξ) σ)
sub ξ (↑ₚ τ) = ↑ₚ sub ξ τ

intro : Term S (takes s) → Sub (S ▷ (takes s)) S
intro e (here refl) = e
intro e (there x) = ` x 

_[_] : Term (S ▷ (takes s)) s → Term S (takes s) → Term S s
e₁ [ e₂ ] = sub (intro e₂) e₁

variable
  ξ ξ' ξ'' ξ₁ ξ₂ : Sub S S₂ 

-- Typing -------------------------------------------------------------------------------

_ₜ : Poly S → Mono S
(∀`α _ ⇒ σ) ₜ = {!   !}
(↑ₚ (` x)) ₜ = ` x
(↑ₚ (t ⇒ _)) ₜ = t 

Unique : Ctx S → OVar S → Poly S → Set
Unique ctx o σ = ∀ {σ'} → σ' ∈ ctx o → ¬ σ' ₜ ≡ {! σ ₜ !}

infixr 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Term S s → Poly S → Set where
  ⊢-`x :  
    wk-ctx Γ x ≡ τ →
    ----------------
    Γ ⊢ ` x ∶ ↑ₚ τ
  ⊢-`o :
    wk-ctx Γ o ≡ Σ →
    σ ∈ Σ →
    ----------------
    Γ ⊢ ` o ∶ σ
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
  ⊢-decl : 
    Γ ▶ ∅ᶜ ⊢ e ∶ wk-σ σ → 
    ----------------
    Γ ⊢ decl`o`in e ∶ σ
  ⊢-inst :
    Γ ⊢ e₂ ∶ σ → 
    (Γ [ o ]⊎ σ) ⊢ e₁ ∶ σ' → 
    Unique Γ o σ →
    ---------------------------------
    Γ ⊢ inst` ` o ∶ σ `= e₂ `in e₁ ∶ σ'
  ⊢-τ :
    Γ ⊢ e ∶ ∀`α c ⇒ σ →
    Γ ⊢ (wk-c c [ τ ]) ∶ σ' →
    -------------------
    Γ ⊢ e ∶ (σ [ τ ])
  ⊢-∀ : 
    (Γ ▶ᶜ c) ⊢ e ∶ σ → 
    ------------------
    Γ ⊢ e ∶ ∀`α c ⇒ wk-σ σ 

-- Environments -------------------------------------------------------------------------



-- Semantics ----------------------------------------------------------------------------

infixr 3 _↓_
data _↓_ : Expr S → Val S → Set where
  ↓-λ :
    λ`x→ e ↓ -λ`x→ e 
{-   ↓-· : 
    e₁ ↓ -λ`x→ e →
    e₂ ↓ v' → 
    e [ ⌞ v' ⌟ ] ↓ v →
    -----------------
    e₁ · e₂ ↓ v
  ↓-let :
    e₂ ↓ v' → 
    e₁ [ ⌞ v' ⌟ ] ↓ v →
    ---------------
    `let`x= e₂ `in e₁ ↓ v    -}