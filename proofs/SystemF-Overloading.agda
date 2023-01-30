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
  τₛ  : Sort ⊤ᶜ

Sorts : Set
Sorts = List (Sort ⊤ᶜ)

variable
  s s' s'' s₁ s₂ : Sort r
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  o o' o'' o₁ o₂ : oₛ ∈ S
  α α' α'' α₁ α₂ : τₛ ∈ S

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
  Λ`α→_           : Term (S ▷ τₛ) eₛ → Term S eₛ
  ƛ_⇒_            : Term S cₛ → Term S eₛ → Term S eₛ 
  _·_             : Term S eₛ → Term S eₛ → Term S eₛ
  _•_             : Term S eₛ → Term S τₛ → Term S eₛ
  _⊘              : Term S eₛ → Term S eₛ
  `let`x=_`in_    : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  decl`o`in_      : Term (S ▷ oₛ) eₛ → Term S eₛ
  inst`_`=_`in_   : Term S oₛ → Term S eₛ → Term S eₛ → Term S eₛ
  _∶_             : Term S oₛ → Term S τₛ → Term S cₛ
  `⊤              : Term S τₛ
  _⇒_             : Term S τₛ → Term S τₛ → Term S τₛ
  ∀`α_            : Term (S ▷ τₛ) τₛ → Term S τₛ
  Ø_⇒_            : Term S cₛ → Term S τₛ → Term S τₛ 

Expr : Sorts → Set
Expr S = Term S eₛ
Cstr : Sorts → Set
Cstr S = Term S cₛ
Type : Sorts → Set
Type S = Term S τₛ

variable
  t t' t'' t₁ t₂ : Term S s
  e e' e'' e₁ e₂ : Expr S
  c c' c'' c₁ c₂ : Cstr S
  τ τ' τ'' τ₁ τ₂ : Type S
 
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
ren ρ (e • τ) = (ren ρ e) • (ren ρ τ)
ren ρ (e ⊘) = (ren ρ e) ⊘
ren ρ (`let`x= e₂ `in e₁) = `let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ (decl`o`in e) = decl`o`in ren (extᵣ ρ) e
ren ρ (inst` o `= e₂ `in e₁) = inst` (ren ρ o) `=  ren ρ e₂ `in ren ρ e₁
ren ρ (o ∶ τ) = ren ρ o ∶ ren ρ τ
ren ρ `⊤ = `⊤
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (∀`α τ) = ∀`α (ren (extᵣ ρ) τ)
ren ρ (Ø c ⇒ τ ) = Ø (ren ρ c) ⇒ (ren ρ τ)

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
extₛ σ (here refl) = ` here refl
extₛ σ (there x) = ren wkᵣ (σ x)

dropₛ : Sub S₁ S₂ → Sub S₁ (S₂ ▷ s) 
dropₛ σ x = wk (σ x)

typeₛ : Sub S₁ S₂ → Type S₂ → Sub (S₁ ▷ τₛ) S₂
typeₛ σ τ (here refl) = τ
typeₛ σ τ (there x) = σ x

sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
sub σ (` x) = (σ x)
sub σ tt = tt
sub σ (λ`x→ e) = λ`x→ (sub (extₛ σ) e)
sub σ (Λ`α→ e) = Λ`α→ (sub (extₛ σ) e)
sub σ (ƛ c ⇒ e) = ƛ sub σ c ⇒ sub σ e 
sub σ (e₁ · e₂) = sub σ e₁ · sub σ e₂
sub σ (e • τ) = sub σ e • sub σ τ
sub σ (e ⊘) = (sub σ e) ⊘
sub σ (`let`x= e₂ `in e₁) = `let`x= sub σ e₂ `in (sub (extₛ σ) e₁)
sub σ (decl`o`in e) = decl`o`in sub (extₛ σ) e
sub σ (inst` o `= e₂ `in e₁) = inst` sub σ o `= sub σ e₂ `in sub σ e₁ 
sub σ (o ∶ τ) = sub σ o ∶ sub σ τ
sub σ `⊤ = `⊤
sub σ (τ₁ ⇒ τ₂) = sub σ τ₁ ⇒ sub σ τ₂
sub σ (∀`α τ) = ∀`α (sub (extₛ σ) τ)
sub σ (Ø c ⇒ τ ) = Ø (sub σ c) ⇒ (sub σ τ)

_[_] : Type (S ▷ τₛ) → Type S → Type S 
τ [ τ' ] = sub (typeₛ idₛ τ') τ

variable
  σ σ' σ'' σ₁ σ₂ : Sub S₁ S₂ 
 
-- Context ------------------------------------------------------------------------------

Stores : Sorts → Sort ⊤ᶜ → Set
Stores S eₛ = Type S
Stores S oₛ = ⊤
Stores S τₛ = ⊤

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
wk-stores {s = eₛ} τ = wk τ
wk-stores {s = oₛ} _ = tt
wk-stores {s = τₛ} _ = tt

wk-stored : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-stored (here refl) t = wk-stores t
wk-stored (there x) t = wk-stores (wk-stored x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-stored x (lookup Γ x)

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S

-- Constraint Solving -------------------------------------------------------------------

data [_]∈_ : Cstr S → Ctx S → Set where
  here : [ (` o ∶ τ) ]∈ (Γ ▸ (` o ∶ τ)) 
  under-bind : {s : Stores S s'} → [ (` o ∶ τ) ]∈ Γ → [ (` there o ∶ wk τ) ]∈ (Γ ▶ s) 
  under-inst : [ c ]∈ Γ → [ c ]∈ (Γ ▸ c')
  
-- Typing -------------------------------------------------------------------------------

Types : Sorts → Sort ⊤ᶜ → Set
Types S eₛ = Type S
Types S oₛ = Type S
Types S τₛ = ⊤

variable 
  T T' T'' T₁ T₂ : Types S s

infix 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Term S s → Types S s → Set where
  ⊢`x :  
    wk-ctx Γ x ≡ τ →
    ----------------
    Γ ⊢ (` x) ∶ τ
  ⊢`o :  
    [ ` o ∶ τ ]∈ Γ →
    -----------------
    Γ ⊢ ` o ∶ τ
  ⊢⊤ : 
    -----------
    Γ ⊢ tt ∶ `⊤
  ⊢λ : 
    Γ ▶ τ ⊢ e ∶ wk τ' →  
    ------------------
    Γ ⊢ λ`x→ e ∶ τ ⇒ τ'
  ⊢Λ : 
    Γ ▶ tt ⊢ e ∶ τ →  
    -------------------
    Γ ⊢ Λ`α→ e ∶ ∀`α τ
  ⊢ƛ : 
    Γ ▸ c ⊢ e ∶ τ →  
    ---------------------
    Γ ⊢ ƛ c ⇒ e ∶ Ø c ⇒ τ
  ⊢· : 
    Γ ⊢ e₁ ∶ τ₁ ⇒ τ₂ →
    Γ ⊢ e₂ ∶ τ₁ →
    ------------------
    Γ ⊢ e₁ · e₂ ∶ τ₂
  ⊢• : 
    Γ ⊢ e ∶ ∀`α τ' →
    --------------------
    Γ ⊢ e • τ ∶ τ' [ τ ]
  ⊢⊘ : 
    Γ ⊢ e ∶ Ø (` o ∶ τ) ⇒ τ' →
    [ ` o ∶ τ ]∈ Γ →
    --------------------------
    Γ ⊢ e ⊘ ∶ τ'
  ⊢let : 
    Γ ⊢ e₂ ∶ τ →
    Γ ▶ τ ⊢ e₁ ∶ wk τ' →
    --------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ τ'
  ⊢decl : 
    Γ ▶ tt ⊢ e ∶ wk τ →
    -------------------
    Γ ⊢ decl`o`in e ∶ τ
  ⊢inst :
    Γ ⊢ e₂ ∶ τ →
    Γ ▸ (` o ∶ τ) ⊢ e₁ ∶ τ' →
    -------------------------------
    Γ ⊢ inst` ` o `= e₂ `in e₁ ∶ τ'    

-- Renaming Typing

ren' : Ren S₁ S₂ → Stores S₁ s → Stores S₂ s
ren' {s = eₛ} ρ τ = ren ρ τ
ren' {s = oₛ} ρ _ = tt
ren' {s = τₛ} ρ _ = tt   

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
  ⊢keep-instᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} → 
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    --------------------------------------
    ρ ∶ (Γ₁ ▸ (o ∶ τ)) ⇒ᵣ (Γ₂ ▸ (ren ρ o ∶ ren ρ τ))
  ⊢drop-instᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} →
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    -------------
    ρ ∶ Γ₁ ⇒ᵣ (Γ₂ ▸ (o ∶ τ))

⊢wkᵣ : ∀ {st : Stores S s} → (dropᵣ idᵣ) ∶ Γ ⇒ᵣ (Γ ▶ st)
⊢wkᵣ = ⊢dropᵣ ⊢idᵣ

⊢wk-instᵣ : ∀ {o} → idᵣ ∶ Γ ⇒ᵣ (Γ ▸ (o ∶ τ))
⊢wk-instᵣ = ⊢drop-instᵣ ⊢idᵣ

-- Substitution Typing ------------------------------------------------------------------

sub' : Sub S₁ S₂ → Stores S₁ s → Stores S₂ s
sub' {s = eₛ} ρ τ = sub ρ τ
sub' {s = oₛ} ρ _ = tt
sub' {s = τₛ} ρ _ = tt

infix 3 _∶_⇒ₛ_
data _∶_⇒ₛ_ : Sub S₁ S₂ → Ctx S₁ → Ctx S₂ -> Set where
  ⊢idₛ : ∀ {Γ} → _∶_⇒ₛ_ {S₁ = S} {S₂ = S} idₛ Γ Γ
  ⊢keepₛ  : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₁ s} → 
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    ----------------------------------
    extₛ σ ∶ Γ₁ ▶ st ⇒ₛ Γ₂ ▶ sub' σ st
  ⊢dropₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {st : Stores S₂ s} →
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    -------------------------
    dropₛ σ ∶ Γ₁ ⇒ₛ (Γ₂ ▶ st) 
  ⊢typeₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ : Type S₂} →
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    --------------
    typeₛ σ τ ∶ Γ₁ ▶ tt ⇒ₛ Γ₂ 
  ⊢keep-instₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} → 
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    --------------------------------------
    σ ∶ (Γ₁ ▸ (o ∶ τ)) ⇒ₛ (Γ₂ ▸ (sub σ o ∶ sub σ τ))
  ⊢drop-instₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} →
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    -------------
    σ ∶ Γ₁ ⇒ₛ (Γ₂ ▸ (o ∶ τ)) 

⊢single-typeₛ : typeₛ idₛ τ ∶ (Γ ▶ tt)  ⇒ₛ Γ
⊢single-typeₛ = ⊢typeₛ ⊢idₛ
