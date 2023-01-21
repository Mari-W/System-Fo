{-# OPTIONS --allow-unsolved-metas #-}

open import Common using (_▷_; _▷▷_)
open import Data.List using (List; []; _∷_; drop; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (Dec; yes; no)

module SystemF.Source where

-- Sorts --------------------------------------------------------------------------------

data Sort : Set where
  eₛ  : Sort 
  oₛ  : Sort
  cₛ  : Sort
  σₛ  : Sort 

Sorts : Set
Sorts = List Sort

variable
  s s' s'' s₁ s₂ : Sort
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  o o' o'' o₁ o₂ : oₛ ∈ S
  α α' α'' α₁ α₂ : σₛ ∈ S

Var : Sorts → Sort → Set
Var S s = s ∈ S

-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ Λ`α_⇒_ `let`x=_`in_ inst`_∶_`=_`in_ ∀`α_⇒_ 
infixr 5 _⇒_ _·_ _•_ _#_ _∶∶_
infix  6 `_ decl`o`in_

data Term : Sorts → Sort → Set where
  `_              : Var S s → Term S s
  tt              : Term S eₛ
  λ`x→_           : Term (S ▷ eₛ) eₛ → Term S eₛ
  Λ`α_⇒_          : Term (S ▷ σₛ) cₛ → Term (S ▷ σₛ) eₛ → Term S eₛ
  _·_             : Term S eₛ → Term S eₛ → Term S eₛ
  _•_             : Term S eₛ → Term S σₛ → Term S eₛ
  `let`x=_`in_    : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  decl`o`in_      : Term (S ▷ oₛ) eₛ → Term S eₛ
  inst`_∶_`=_`in_ : Term S oₛ → Term S σₛ → Term S eₛ → Term S eₛ → Term S eₛ
  ε               : Term S cₛ
  _∶∶_             : Term S oₛ → Term S σₛ → Term S cₛ
  _#_             : Term S cₛ → Term S cₛ → Term S cₛ
  `⊤              : Term S σₛ
  _⇒_             : Term S σₛ → Term S σₛ → Term S σₛ
  ∀`α_⇒_          : Term (S ▷ σₛ) cₛ → Term (S ▷ σₛ) σₛ → Term S σₛ

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

extᵣ : Ren S₁ S₂ → Ren (S₁ ▷ s) (S₂ ▷ s)
extᵣ ρ (here refl) = here refl
extᵣ ρ (there x) = there (ρ x)

wkᵣ : Ren S (S ▷ s) 
wkᵣ = there

ren : Ren S₁ S₂ → (Term S₁ s → Term S₂ s)
ren ρ (` x) = ` (ρ x)
ren ρ tt = tt
ren ρ (λ`x→ e) = λ`x→ (ren (extᵣ ρ) e)
ren ρ (Λ`α c ⇒ e) = Λ`α (ren (extᵣ ρ) c) ⇒ (ren (extᵣ ρ) e)
ren ρ (e₁ · e₂) = (ren ρ e₁) · (ren ρ e₂)
ren ρ (e • σ) = (ren ρ e) • (ren ρ σ)
ren ρ (`let`x= e₂ `in e₁) = `let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ (decl`o`in e) = decl`o`in ren (extᵣ ρ) e
ren ρ (inst` o ∶ σ `= e₂ `in e₁) = inst` (ren ρ o) ∶ ren ρ σ `=  ren ρ e₂ `in ren ρ e₁
ren ρ ε = ε 
ren ρ (o ∶∶ σ) = ren ρ o ∶∶ ren ρ σ
ren ρ (c₁ # c₂) = ren ρ c₁ # ren ρ c₂
ren ρ `⊤ = `⊤
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (∀`α c ⇒ σ) = ∀`α (ren (extᵣ ρ) c) ⇒ (ren (extᵣ ρ) σ)

wk : Term S s → Term (S ▷ s') s
wk = ren there

-- Substitution -------------------------------------------------------------------------

binds : Sort → Sort 
binds eₛ = eₛ
binds oₛ = eₛ
binds cₛ = σₛ
binds σₛ = σₛ

Sub : Sorts → Sorts → Set
Sub S₁ S₂ = ∀ {s} → Var S₁ s → Term S₂ s

extₛ : Sub S₁ S₂ → Sub (S₁ ▷ s) (S₂ ▷ s)
extₛ ξ (here refl) = ` here refl
extₛ ξ (there x) = ren wkᵣ (ξ x)

sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
sub ξ (` x) = (ξ x)
sub ξ tt = tt
sub ξ (λ`x→ e) = λ`x→ (sub (extₛ ξ) e)
sub ξ (Λ`α c ⇒ e) = Λ`α sub (extₛ ξ) c ⇒ (sub (extₛ ξ) e)
sub ξ (e₁ · e₂) = sub ξ e₁ · sub ξ e₂
sub ξ (e • σ) = sub ξ e • sub ξ σ
sub ξ (`let`x= e₂ `in e₁) = `let`x= sub ξ e₂ `in (sub (extₛ ξ) e₁)
sub ξ (decl`o`in e) = decl`o`in sub (extₛ ξ) e
sub ξ (inst` o ∶ σ `= e₂ `in e₁) = inst` sub ξ o ∶ sub ξ σ `= sub ξ e₂ `in sub ξ e₁ 
sub ξ ε = ε 
sub ξ (o ∶∶ σ) = sub ξ o ∶∶ sub ξ σ
sub ξ (c₁ # c₂) = sub ξ c₁ # sub ξ c₂
sub ξ `⊤ = `⊤
sub ξ (τ₁ ⇒ τ₂) = sub ξ τ₁ ⇒ sub ξ τ₂
sub ξ (∀`α c ⇒ σ) = ∀`α sub (extₛ ξ) c ⇒ (sub (extₛ ξ) σ)

intro :  Term S (binds s) → Sub (S ▷ (binds s)) S
intro e (here refl) = e
intro e (there x) = ` x 

_[_] : Term (S ▷ (binds s)) s → Term S (binds s) → Term S s
e₁ [ e₂ ] = sub (intro e₂) e₁

variable
  ξ ξ' ξ'' ξ₁ ξ₂ : Sub S S₂ 

-- Equality -----------------------------------------------------------------------------

{- mutual 
  _≡x_ : (x x' : Var S s) → Dec (x ≡ x')
  here refl ≡x here refl = yes refl
  here refl ≡x there x' = no (λ ())
  there x ≡x here refl = no (λ ())
  there x ≡x there x' with x ≡x x' 
  ... | yes refl = yes refl
  ... | no x = no λ { refl → x refl }

  _≡c_ : (c c' : Cstr S) → Dec (c ≡ c')
  (` x) ≡c (` x') with x ≡x x'
  ... | yes refl = yes refl
  ... | no x = no λ { refl → x refl }
  (` x) ≡c ε = no (λ ())
  (` x) ≡c (c' ∶∶ c'') = no (λ ())
  (` x) ≡c (c' # c'') = no (λ ())
  ε ≡c (` x) = no (λ ())
  ε ≡c ε = yes refl
  ε ≡c (c' ∶∶ c'') = no (λ ())
  ε ≡c (c' # c'') = no (λ ())
  (o ∶∶ σ) ≡c (` x) = no (λ ())
  (o ∶∶ σ) ≡c ε = no (λ ())
  ((` o) ∶∶ σ) ≡c ((` o') ∶∶ σ') with o ≡x o' | σ ≡σ σ' 
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no x = no λ { refl → x refl }
  ... | no x | yes refl = no λ { refl → x refl }
  ... | no x | no x' = no λ { refl → x refl }
  (o ∶∶ σ) ≡c (c # c') = no (λ ())
  (c # c') ≡c (` x) = no (λ ())
  (c # c') ≡c ε = no (λ ())
  (c # c') ≡c (o ∶∶ σ) = no (λ ())
  (c # c'') ≡c (c' # c''') with c ≡c c' | c'' ≡c c''' 
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no x = no λ { refl → x refl }
  ... | no x | yes refl = no λ { refl → x refl }
  ... | no x | no x' = no λ { refl → x refl }

  _≡σ_ : (σ σ' : Type S) → Dec (σ ≡ σ')
  (` x) ≡σ (` x') with x ≡x x'
  ... | yes refl = yes refl
  ... | no x = no λ { refl → x refl }
  (` x) ≡σ `⊤ = no (λ ())
  (` x) ≡σ (σ' ⇒ σ'') = no (λ ())
  (` x) ≡σ (∀`α σ' ⇒ σ'') = no (λ ())
  `⊤ ≡σ (` x) = no (λ ())
  `⊤ ≡σ `⊤ = yes refl
  `⊤ ≡σ (σ' ⇒ σ'') = no (λ ())
  `⊤ ≡σ (∀`α σ' ⇒ σ'') = no (λ ())
  (σ ⇒ σ') ≡σ (` x) = no (λ ())
  (σ ⇒ σ') ≡σ `⊤ = no (λ ())
  (σ ⇒ σ'') ≡σ (σ' ⇒ σ''') with σ ≡σ σ' | σ'' ≡σ σ''' 
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no x = no λ { refl → x refl }
  ... | no x | yes refl = no λ { refl → x refl }
  ... | no x | no x' = no λ { refl → x refl }
  (σ ⇒ σ₁) ≡σ (∀`α σ' ⇒ σ'') = no (λ ())
  (∀`α c ⇒ σ) ≡σ (` x) = no (λ ())
  (∀`α c ⇒ σ) ≡σ `⊤ = no (λ ())
  (∀`α c ⇒ σ) ≡σ (σ' ⇒ σ'') = no (λ ())
  (∀`α c ⇒ σ) ≡σ (∀`α c' ⇒ σ') with c ≡c c' | σ ≡σ σ' 
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no x = no λ { refl → x refl }
  ... | no x | yes refl = no λ { refl → x refl }
  ... | no x | no x' = no λ { refl → x refl }
 -}
 
-- Context ------------------------------------------------------------------------------

Stores : Sorts → Sort → Set
Stores S eₛ = Type S
Stores S oₛ = ⊤
Stores S cₛ = ⊥
Stores S σₛ = ⊤

data Ctx : Sorts → Set where
  ∅   : Ctx []
  _▶_ : Ctx S → Stores S s → Ctx (S ▷ s)
  _▸_ : Ctx S → (Var S oₛ × Type S) → Ctx S

_▸*_ : Ctx S → Cstr S → Ctx S
Γ ▸* (` x) = Γ
Γ ▸* ε = Γ
Γ ▸* (` o ∶∶ σ) = Γ ▸ (o , σ)
Γ ▸* (c₁ # c₂) = (Γ ▸* c₁) ▸* c₂

depth : Var S s → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

drop-last : ∀ {S s} → Var S s → Sorts → Sorts
drop-last = drop ∘ suc ∘ depth

lookup : Ctx S → (v : Var S s) → Stores (drop-last v S) s 
lookup (Γ ▶ x) (here refl) = x
lookup (Γ ▶ x) (there t) = lookup Γ t
lookup (Γ ▸ x) t = lookup Γ t

wk-item : Stores S s → Stores (S ▷ s') s
wk-item {s = eₛ} σ = wk σ
wk-item {s = oₛ} _ = tt
wk-item {s = σₛ} _ = tt

wk-stored : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-stored (here refl) t = wk-item t
wk-stored (there x) t = wk-item (wk-stored x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-stored x (lookup Γ x)

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S

-- Constraint Solving -----------------------------------------------------------------

_≡x_ : (x x' : Var S s) → Dec (x ≡ x')
here refl ≡x here refl = yes refl
here refl ≡x there x' = no (λ ())
there x ≡x here refl = no (λ ())
there x ≡x there x' with x ≡x x' 
... | yes refl = yes refl
... | no x = no λ { refl → x refl }

resolve : Ctx S → Var S oₛ → List (Type S)
resolve (Γ ▶ x) (here refl) = []
resolve (Γ ▶ x) (there o) = map wk (resolve Γ o)
resolve (Γ ▸ (o' , σ)) o with o' ≡x o 
... | yes refl = (resolve Γ o) ▷ σ
... | no _ = (resolve Γ o)

-- Typing -------------------------------------------------------------------------------

infixr 3 _⊢_
data _⊢_ : Ctx S → Cstr S → Set where
  ⊢–ε : 
    ----------
    Γ ⊢ ε
  ⊢–∶∶ : 
    σ ∈ resolve Γ o →
    ----------------------
    Γ ⊢ (` o ∶∶ σ)
  ⊢–# : 
    Γ ⊢ c₁ →
    Γ ⊢ c₂ →
    -------------
    Γ ⊢ (c₁ # c₂)

infixr 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Term S s → Type S → Set where
  ⊢-`x :  
    wk-ctx Γ x ≡ σ →
    ----------------
    Γ ⊢ (` x) ∶ σ
  ⊢-`o :  
    σ ∈ resolve Γ o →
    -----------------
    Γ ⊢ ` o ∶ σ
  ⊢-⊤ : 
    -----------
    Γ ⊢ tt ∶ `⊤
  ⊢-λ : 
    Γ ▶ σ ⊢ e ∶ wk σ →  
    ------------------
    Γ ⊢ λ`x→ e ∶ σ
  ⊢-Λ : 
    (Γ ▶ tt) ▸* c ⊢ e ∶ σ →  
    -------------------------
    Γ ⊢ Λ`α c ⇒ e ∶ ∀`α c ⇒ σ
  ⊢-· : 
    Γ ⊢ e₁ ∶ σ₁ ⇒ σ₂ →
    Γ ⊢ e₂ ∶ σ₁ →
    ------------------
    Γ ⊢ e₁ · e₂ ∶ σ₂
  ⊢-• : 
    Γ ⊢ e ∶ ∀`α c ⇒ σ' →
    Γ ⊢ c [ σ ] →
    --------------------
    Γ ⊢ e • σ ∶ σ' [ σ ]
  ⊢-let : 
    Γ ⊢ e₂ ∶ σ →
    Γ ▶ σ ⊢ e₁ ∶ wk σ' →
    --------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ σ'
  ⊢-decl : 
    Γ ▶ tt ⊢ e ∶ wk σ →
    -------------------
    Γ ⊢ decl`o`in e ∶ σ
  ⊢-inst :
    Γ ⊢ e₂ ∶ σ' →
    Γ ▸ (o , σ) ⊢ e₁ ∶ σ →
    ----------------------------------
    Γ ⊢ inst` ` o ∶ σ `= e₂ `in e₁ ∶ σ   