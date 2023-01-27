open import Common using (_▷_; _▷▷_; Ctxable; ⊤ᶜ; ⊥ᶜ; r)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (id; _∘_)

module SystemF-Overloading where

-- Sorts --------------------------------------------------------------------------------

data Sort : Ctxable → Set where
  eₛ  : Sort ⊤ᶜ
  oₛ  : Sort ⊤ᶜ
  cₛ  : Sort ⊥ᶜ
  σₛ  : Sort ⊤ᶜ

Sorts : Set
Sorts = List (Sort ⊤ᶜ)

variable
  s s' s'' s₁ s₂ : Sort r
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  o o' o'' o₁ o₂ : oₛ ∈ S
  α α' α'' α₁ α₂ : σₛ ∈ S

Var : Sorts → Sort ⊤ᶜ → Set
Var S s = s ∈ S

-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ Λ`α→_ `let`x=_`in_ inst`_`=_`in_ ∀`α_ _∶_
infixr 5 _⇒_ _·_ _•_ 
infix  6 `_ decl`o`in_ _⊘

data Term : Sorts → Sort r → Set where
  `_              : Var S s → Term S s
  tt              : Term S eₛ
  λ`x→_           : Term (S ▷ eₛ) eₛ → Term S eₛ
  Λ`α→_           : Term (S ▷ σₛ) eₛ → Term S eₛ
  ƛ_⇒_            : Term S cₛ → Term S eₛ → Term S eₛ 
  _·_             : Term S eₛ → Term S eₛ → Term S eₛ
  _•_             : Term S eₛ → Term S σₛ → Term S eₛ
  _⊘              : Term S eₛ → Term S eₛ
  `let`x=_`in_    : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  decl`o`in_      : Term (S ▷ oₛ) eₛ → Term S eₛ
  inst`_`=_`in_   : Term S oₛ → Term S eₛ → Term S eₛ → Term S eₛ
  _∶_             : Term S oₛ → Term S σₛ → Term S cₛ
  `⊤              : Term S σₛ
  _⇒_             : Term S σₛ → Term S σₛ → Term S σₛ
  ∀`α_            : Term (S ▷ σₛ) σₛ → Term S σₛ
  Ø_⇒_            : Term S cₛ → Term S σₛ → Term S σₛ 

Expr : Sorts → Set
Expr S = Term S eₛ
Cstr : Sorts → Set
Cstr S = Term S cₛ
Type : Sorts → Set
Type S = Term S σₛ

variable
  t t' t'' t₁ t₂ : Term S s
  e e' e'' e₁ e₂ : Expr S
  c c' c'' c₁ c₂ : Cstr S
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
ren ρ (ƛ c ⇒ e) = ƛ ren ρ c ⇒ ren ρ e 
ren ρ (e₁ · e₂) = (ren ρ e₁) · (ren ρ e₂)
ren ρ (e • σ) = (ren ρ e) • (ren ρ σ)
ren ρ (e ⊘) = (ren ρ e) ⊘
ren ρ (`let`x= e₂ `in e₁) = `let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ (decl`o`in e) = decl`o`in ren (extᵣ ρ) e
ren ρ (inst` o `= e₂ `in e₁) = inst` (ren ρ o) `=  ren ρ e₂ `in ren ρ e₁
ren ρ (o ∶ σ) = ren ρ o ∶ ren ρ σ
ren ρ `⊤ = `⊤
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (∀`α σ) = ∀`α (ren (extᵣ ρ) σ)
ren ρ (Ø c ⇒ σ ) = Ø (ren ρ c) ⇒ (ren ρ σ)

wk : Term S s → Term (S ▷ s') s
wk = ren there

variable
  ρ ρ' ρ'' ρ₁ ρ₂ : Ren S₁ S₂ 
 

-- Substitution -------------------------------------------------------------------------

Sub : Sorts → Sorts → Set
Sub S₁ S₂ = ∀ {s} → Var S₁ s → Term S₂ s

idₛ : Sub S S
idₛ = `_

extₛ : Sub S₁ S₂ → Sub (S₁ ▷ s) (S₂ ▷ s)
extₛ ξ (here refl) = ` here refl
extₛ ξ (there x) = ren wkᵣ (ξ x)

dropₛ : Sub S₁ S₂ → Sub S₁ (S₂ ▷ s) 
dropₛ ξ x = wk (ξ x)

typeₛ : Sub S₁ S₂ → Type S₂ → Sub (S₁ ▷ σₛ) S₂
typeₛ ξ σ (here refl) = σ
typeₛ ξ σ (there x) = ξ x

sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
sub ξ (` x) = (ξ x)
sub ξ tt = tt
sub ξ (λ`x→ e) = λ`x→ (sub (extₛ ξ) e)
sub ξ (Λ`α→ e) = Λ`α→ (sub (extₛ ξ) e)
sub ξ (ƛ c ⇒ e) = ƛ sub ξ c ⇒ sub ξ e 
sub ξ (e₁ · e₂) = sub ξ e₁ · sub ξ e₂
sub ξ (e • σ) = sub ξ e • sub ξ σ
sub ξ (e ⊘) = (sub ξ e) ⊘
sub ξ (`let`x= e₂ `in e₁) = `let`x= sub ξ e₂ `in (sub (extₛ ξ) e₁)
sub ξ (decl`o`in e) = decl`o`in sub (extₛ ξ) e
sub ξ (inst` o `= e₂ `in e₁) = inst` sub ξ o `= sub ξ e₂ `in sub ξ e₁ 
sub ξ (o ∶ σ) = sub ξ o ∶ sub ξ σ
sub ξ `⊤ = `⊤
sub ξ (τ₁ ⇒ τ₂) = sub ξ τ₁ ⇒ sub ξ τ₂
sub ξ (∀`α σ) = ∀`α (sub (extₛ ξ) σ)
sub ξ (Ø c ⇒ σ ) = Ø (sub ξ c) ⇒ (sub ξ σ)

introduce :  Term S s → Sub (S ▷ s) S
introduce e (here refl) = e
introduce e (there x) = ` x 

_[_] : Term (S ▷ s') s → Term S s' → Term S s
t [ t' ] = sub (introduce t') t

variable
  ξ ξ' ξ'' ξ₁ ξ₂ : Sub S₁ S₂ 
 
-- Context ------------------------------------------------------------------------------

Stores : Sorts → Sort ⊤ᶜ → Set
Stores S eₛ = Type S
Stores S oₛ = ⊤
Stores S σₛ = ⊤

data Ctx : Sorts → Set where
  ∅   : Ctx []
  _▶_ : Ctx S → Stores S s → Ctx (S ▷ s)
  _▸_ : Ctx S → Cstr S → Ctx S

depth : Var S s → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

drop-last : ∀ {S s} → Var S s → Sorts → Sorts
drop-last = drop ∘ suc ∘ depth

lookup : Ctx S → (v : Var S s) → Stores (drop-last v S) s 
lookup (Γ ▶ x) (here refl) = x
lookup (Γ ▶ x) (there t) = lookup Γ t
lookup (Γ ▸ x) t = lookup Γ t

wk-stores : Stores S s → Stores (S ▷ s') s
wk-stores {s = eₛ} σ = wk σ
wk-stores {s = oₛ} _ = tt
wk-stores {s = σₛ} _ = tt

wk-stored : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-stored (here refl) t = wk-stores t
wk-stored (there x) t = wk-stores (wk-stored x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-stored x (lookup Γ x)

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S

-- Constraint Solving -------------------------------------------------------------------

data [_]∈_ : Cstr S → Ctx S → Set where
  here : [ (` o ∶ σ) ]∈ (Γ ▸ (` o ∶ σ)) 
  under-bind : {s : Stores S s'} → [ (` o ∶ σ) ]∈ Γ → [ (` there o ∶ wk σ) ]∈ (Γ ▶ s) 
  under-inst : [ c ]∈ Γ → [ c ]∈ (Γ ▸ c')
  
-- Typing -------------------------------------------------------------------------------

Types : Sorts → Sort ⊤ᶜ → Set
Types S eₛ = Type S
Types S oₛ = Type S
Types S σₛ = ⊤

variable 
  T T' T'' T₁ T₂ : Types S s

infix 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Term S s → Types S s → Set where
  ⊢`x :  
    wk-ctx Γ x ≡ σ →
    ----------------
    Γ ⊢ (` x) ∶ σ
  ⊢`o :  
    [ ` o ∶ σ ]∈ Γ →
    -----------------
    Γ ⊢ ` o ∶ σ
  ⊢⊤ : 
    -----------
    Γ ⊢ tt ∶ `⊤
  ⊢λ : 
    Γ ▶ σ ⊢ e ∶ wk σ' →  
    ------------------
    Γ ⊢ λ`x→ e ∶ σ ⇒ σ'
  ⊢Λ : 
    Γ ▶ tt ⊢ e ∶ σ →  
    -------------------
    Γ ⊢ Λ`α→ e ∶ ∀`α σ
  ⊢ƛ : 
    Γ ▸ c ⊢ e ∶ σ →  
    ---------------------
    Γ ⊢ ƛ c ⇒ e ∶ Ø c ⇒ σ
  ⊢· : 
    Γ ⊢ e₁ ∶ σ₁ ⇒ σ₂ →
    Γ ⊢ e₂ ∶ σ₁ →
    ------------------
    Γ ⊢ e₁ · e₂ ∶ σ₂
  ⊢• : 
    Γ ⊢ e ∶ ∀`α σ' →
    --------------------
    Γ ⊢ e • σ ∶ σ' [ σ ]
  ⊢⊘ : 
    Γ ⊢ e ∶ Ø (` o ∶ σ) ⇒ σ' →
    [ ` o ∶ σ ]∈ Γ →
    --------------------------
    Γ ⊢ e ⊘ ∶ σ'
  ⊢let : 
    Γ ⊢ e₂ ∶ σ →
    Γ ▶ σ ⊢ e₁ ∶ wk σ' →
    --------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ σ'
  ⊢decl : 
    Γ ▶ tt ⊢ e ∶ wk σ →
    -------------------
    Γ ⊢ decl`o`in e ∶ σ
  ⊢inst :
    Γ ⊢ e₂ ∶ σ →
    Γ ▸ (` o ∶ σ) ⊢ e₁ ∶ σ' →
    -------------------------------
    Γ ⊢ inst` ` o `= e₂ `in e₁ ∶ σ'    

-- Renaming Typing

ren' : Ren S₁ S₂ → Stores S₁ s → Stores S₂ s
ren' {s = eₛ} ρ σ = ren ρ σ
ren' {s = oₛ} ρ _ = tt
ren' {s = σₛ} ρ _ = tt   

infix 3 _∶_⇒ᵣ_
data _∶_⇒ᵣ_ : Ren S₁ S₂ → Ctx S₁ → Ctx S₂ -> Set where
  ⊢idᵣ : ∀ {Γ} → _∶_⇒ᵣ_ {S₁ = S} {S₂ = S} idᵣ Γ Γ
  ⊢keepᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₁ s} → 
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    --------------------------------------
    extᵣ ρ ∶ Γ₁ ▶ st ⇒ᵣ Γ₂ ▶ ren' ρ st
  ⊢dropᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₂ s} →
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    -------------
    dropᵣ ρ ∶ Γ₁ ⇒ᵣ Γ₂ ▶ st
  ⊢keep-instᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {σ} {o} → 
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    --------------------------------------
    ρ ∶ (Γ₁ ▸ (` o ∶ σ)) ⇒ᵣ (Γ₂ ▸ (` ρ o ∶ ren ρ σ))
  ⊢drop-instᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {σ} {o} →
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    -------------
    ρ ∶ Γ₁ ⇒ᵣ (Γ₂ ▸ (` o ∶ σ))

⊢wkᵣ : ∀ {st : Stores S s} → (dropᵣ idᵣ) ∶ Γ ⇒ᵣ (Γ ▶ st)
⊢wkᵣ = ⊢dropᵣ ⊢idᵣ

⊢wk-instᵣ : idᵣ ∶ Γ ⇒ᵣ (Γ ▸ (` o ∶ σ))
⊢wk-instᵣ = ⊢drop-instᵣ ⊢idᵣ

-- Substitution Typing ------------------------------------------------------------------

sub' : Sub S₁ S₂ → Stores S₁ s → Stores S₂ s
sub' {s = eₛ} ρ σ = sub ρ σ
sub' {s = oₛ} ρ _ = tt
sub' {s = σₛ} ρ _ = tt

infix 3 _∶_⇒ₛ_
data _∶_⇒ₛ_ : Sub S₁ S₂ → Ctx S₁ → Ctx S₂ -> Set where
  ⊢idₛ : ∀ {Γ} → _∶_⇒ₛ_ {S₁ = S} {S₂ = S} idₛ Γ Γ
  ⊢keepₛ  : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₁ s} → 
    ξ ∶ Γ₁ ⇒ₛ Γ₂ →
    ----------------------------------
    extₛ ξ ∶ Γ₁ ▶ st ⇒ₛ Γ₂ ▶ sub' ξ st
  ⊢dropₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₂ s} →
    ξ ∶ Γ₁ ⇒ₛ Γ₂ →
    -------------------------
    dropₛ ξ ∶ Γ₁ ⇒ₛ (Γ₂ ▶ st) 
  ⊢typeₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {σ : Type S₂} →
    ξ ∶ Γ₁ ⇒ₛ Γ₂ →
    --------------
    typeₛ ξ σ ∶ Γ₁ ▶ tt ⇒ₛ Γ₂ 
  ⊢keep-instₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {σ} {o} → 
    ξ ∶ Γ₁ ⇒ₛ Γ₂ →
    --------------------------------------
    ξ ∶ (Γ₁ ▸ (` o ∶ σ)) ⇒ₛ (Γ₂ ▸ (ξ o ∶ sub ξ σ))
  ⊢drop-instₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {σ} {o} →
    ξ ∶ Γ₁ ⇒ₛ Γ₂ →
    -------------
    ξ ∶ Γ₁ ⇒ₛ (Γ₂ ▸ (` o ∶ σ)) 

