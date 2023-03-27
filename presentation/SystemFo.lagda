\begin{code}[hide]
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans)
open import Function using (id; _∘_)

module SystemFo where

-- Sorts --------------------------------------------------------------------------------
data Bindable : Set where
  B : Bindable
  ¬B : Bindable

variable
  r r' r'' r₁ r₂ : Bindable
\end{code}
\newcommand{\FoSort}[0]{\begin{code}
data Sort : Bindable → Set where
  oₛ  : Sort B
  cₛ  : Sort ¬B
  -- ...
\end{code}}
\begin{code}[hide]
  eₛ  : Sort B
  τₛ  : Sort B
  κₛ  : Sort ¬B
\end{code}
\begin{code}[hide]
Sorts : Set
Sorts = List (Sort B)

infix 25 _▷_ _▷▷_
pattern _▷_ xs x = x ∷ xs
_▷▷_ : {A : Set} → List A → List A → List A
xs ▷▷ ys = ys ++ xs

variable
  s s' s'' s₁ s₂ : Sort r
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  o o' o'' o₁ o₂ : oₛ ∈ S
  α α' α'' α₁ α₂ : τₛ ∈ S

Var : Sorts → Sort B → Set
Var S s = s ∈ S  

-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ Λ`α→_ let`x=_`in_ inst`_`=_`in_ ∀`α_ _∶_
infixr 5 _⇒_ _·_ _•_ 
infix  6 `_ decl`o`in_
\end{code}
\newcommand{\FoTerm}[0]{\begin{code}
data Term : Sorts → Sort r → Set where
  `_              : s ∈ S → Term S s
  decl`o`in_      : Term (S ▷ oₛ) eₛ → Term S eₛ
  inst`_`=_`in_   : Term S oₛ → Term S eₛ → Term S eₛ → Term S eₛ
  _∶_             : Term S oₛ → Term S τₛ → Term S cₛ
  ƛ_⇒_            : Term S cₛ → Term S eₛ → Term S eₛ 
  [_]⇒_           : Term S cₛ → Term S τₛ → Term S τₛ
\end{code}}
\begin{code}[hide]
  -- TODO HIDE `_
  tt              : Term S eₛ
  λ`x→_           : Term (S ▷ eₛ) eₛ → Term S eₛ
  Λ`α→_           : Term (S ▷ τₛ) eₛ → Term S eₛ
  _·_             : Term S eₛ → Term S eₛ → Term S eₛ
  _•_             : Term S eₛ → Term S τₛ → Term S eₛ
  let`x=_`in_     : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  `⊤              : Term S τₛ
  _⇒_             : Term S τₛ → Term S τₛ → Term S τₛ
  ∀`α_            : Term (S ▷ τₛ) τₛ → Term S τₛ
  ⋆               : Term S κₛ

Expr : Sorts → Set
Expr S = Term S eₛ
Cstr : Sorts → Set
\end{code}
\newcommand{\FoCstr}[0]{\begin{code}[inline]
Cstr S = Term S cₛ
\end{code}}
\begin{code}[hide]
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
ren ρ (let`x= e₂ `in e₁) = let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ (decl`o`in e) = decl`o`in ren (extᵣ ρ) e
ren ρ (inst` o `= e₂ `in e₁) = inst` (ren ρ o) `=  ren ρ e₂ `in ren ρ e₁
ren ρ (o ∶ τ) = ren ρ o ∶ ren ρ τ
ren ρ `⊤ = `⊤
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
ren ρ (∀`α τ) = ∀`α (ren (extᵣ ρ) τ)
ren ρ ([ c ]⇒ τ) = [ ren ρ c ]⇒ (ren ρ τ)
ren ρ ⋆ = ⋆

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

single-typeₛ : Sub S₁ S₂ → Type S₂ → Sub (S₁ ▷ τₛ) S₂
single-typeₛ σ τ (here refl) = τ
single-typeₛ σ τ (there x) = σ x

sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
sub σ (` x) = (σ x)
sub σ tt = tt
sub σ (λ`x→ e) = λ`x→ (sub (extₛ σ) e)
sub σ (Λ`α→ e) = Λ`α→ (sub (extₛ σ) e)
sub σ (ƛ c ⇒ e) = ƛ sub σ c ⇒ sub σ e 
sub σ (e₁ · e₂) = sub σ e₁ · sub σ e₂
sub σ (e • τ) = sub σ e • sub σ τ
sub σ (let`x= e₂ `in e₁) = let`x= sub σ e₂ `in (sub (extₛ σ) e₁)
sub σ (decl`o`in e) = decl`o`in sub (extₛ σ) e
sub σ (inst` o `= e₂ `in e₁) = inst` sub σ o `= sub σ e₂ `in sub σ e₁ 
sub σ (o ∶ τ) = sub σ o ∶ sub σ τ
sub σ `⊤ = `⊤
sub σ (τ₁ ⇒ τ₂) = sub σ τ₁ ⇒ sub σ τ₂
sub σ (∀`α τ) = ∀`α (sub (extₛ σ) τ)
sub σ ([ c ]⇒ τ ) = [ sub σ c ]⇒ (sub σ τ)
sub σ ⋆ = ⋆
\end{code}
\newcommand{\Fosubs}[0]{\begin{code}
_[_] : Type (S ▷ τₛ) → Type S → Type S 
τ [ τ' ] = sub (single-typeₛ idₛ τ') τ
\end{code}}
\begin{code}[hide]
variable
  σ σ' σ'' σ₁ σ₂ : Sub S₁ S₂ 
 
-- Context ------------------------------------------------------------------------------

item-Bindable : Sort B → Bindable
item-Bindable eₛ = B
item-Bindable τₛ = ¬B
item-Bindable oₛ = ¬B

item-of : (s : Sort B) → Sort (item-Bindable s)
\end{code}
\newcommand{\Foitem}[0]{\begin{code}
item-of eₛ = τₛ
item-of τₛ = κₛ
item-of oₛ = κₛ
\end{code}}
\begin{code}[hide]
variable
  I I' I'' I₁ I₂ : Term S (item-of s)
\end{code}
\newcommand{\FoCtx}[0]{\begin{code}
data Ctx : Sorts → Set where
  ∅   : Ctx []
  _▶_ : Ctx S → Term S (item-of s) → Ctx (S ▷ s)
  _▸_ : Ctx S → Cstr S → Ctx S
\end{code}}
\begin{code}[hide]
lookup : Ctx S → Var S s → Term S (item-of s) 
lookup (Γ ▶ S) (here refl) = wk S
lookup (Γ ▶ S) (there x) = wk (lookup Γ x)
lookup (Γ ▸ c) x = lookup Γ x

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S

-- Constraint Solving -------------------------------------------------------------------
\end{code}
\newcommand{\FoCstrSolve}[0]{\begin{code}
data [_]∈_ : Cstr S → Ctx S → Set where
  here : [ (` o ∶ τ) ]∈ (Γ ▸ (` o ∶ τ)) 
  under-bind : {I : Term S (item-of s')} → [ (` o ∶ τ) ]∈ Γ → [ (` there o ∶ wk τ) ]∈ (Γ ▶ I) 
  under-cstr : [ c ]∈ Γ → [ c ]∈ (Γ ▸ c')
\end{code}}
\begin{code}[hide]
-- Typing -------------------------------------------------------------------------------

kind-Bindable : Sort B → Bindable
kind-Bindable eₛ = B
kind-Bindable τₛ = ¬B
kind-Bindable oₛ = B

type-of : (s : Sort B) → Sort (kind-Bindable s)
\end{code}
\newcommand{\Fokind}[0]{\begin{code}
type-of eₛ = τₛ
type-of τₛ = κₛ
type-of oₛ = τₛ
\end{code}}
\begin{code}[hide]
variable 
  T T' T'' T₁ T₂ : Term S (type-of s)


infix 3 _⊢_∶_
\end{code}
\newcommand{\FoTyping}[0]{\begin{code}
data _⊢_∶_ : Ctx S → Term S s → Term S (type-of s) → Set where
  ⊢inst :
    Γ ⊢ e₂ ∶ τ →
    Γ ▸ (` o ∶ τ) ⊢ e₁ ∶ τ' →
    Γ ⊢ inst` ` o `= e₂ `in e₁ ∶ τ'
  ⊢`o :  
    [ ` o ∶ τ ]∈ Γ →
    Γ ⊢ ` o ∶ τ
  ⊢ƛ : 
    Γ ▸ c ⊢ e ∶ τ →  
    Γ ⊢ ƛ c ⇒ e ∶ [ c ]⇒ τ
  ⊢⊘ : 
    Γ ⊢ e ∶ [ ` o ∶ τ ]⇒ τ' →
    [ ` o ∶ τ ]∈ Γ →
    Γ ⊢ e ∶ τ'
\end{code}}
\begin{code}[hide]
  -- TODO REMOVE THIS ^^^^^^  
  ⊢decl : 
    Γ ▶ ⋆ ⊢ e ∶ wk τ →
    Γ ⊢ decl`o`in e ∶ τ
  -- ...
\end{code}
\begin{code}[hide]
  ⊢`x :  
    lookup Γ x ≡ τ →
    ----------------
    Γ ⊢ (` x) ∶ τ
  ⊢⊤ : 
    -----------
    Γ ⊢ tt ∶ `⊤
  ⊢λ : 
    Γ ▶ τ ⊢ e ∶ wk τ' →  
    ------------------
    Γ ⊢ λ`x→ e ∶ τ ⇒ τ'
  ⊢Λ : 
    Γ ▶ ⋆ ⊢ e ∶ τ →  
    -------------------
    Γ ⊢ Λ`α→ e ∶ ∀`α τ
  ⊢· : 
    Γ ⊢ e₁ ∶ τ₁ ⇒ τ₂ →
    Γ ⊢ e₂ ∶ τ₁ →
    ------------------
    Γ ⊢ e₁ · e₂ ∶ τ₂
  ⊢• : 
    Γ ⊢ e ∶ ∀`α τ' →
    --------------------
    Γ ⊢ e • τ ∶ τ' [ τ ]
  ⊢let : 
    Γ ⊢ e₂ ∶ τ →
    Γ ▶ τ ⊢ e₁ ∶ wk τ' →
    --------------------------
    Γ ⊢ let`x= e₂ `in e₁ ∶ τ'


-- Renaming Typing


infix 3 _∶_⇒ᵣ_
\end{code}
\newcommand{\FoRenTyping}[0]{\begin{code}
data _∶_⇒ᵣ_ : Ren S₁ S₂ → Ctx S₁ → Ctx S₂ -> Set where
  ⊢ext-cstrᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} → 
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    --------------------------------------
    ρ ∶ (Γ₁ ▸ (o ∶ τ)) ⇒ᵣ (Γ₂ ▸ (ren ρ o ∶ ren ρ τ))
  ⊢drop-cstrᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} →
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    -------------
    ρ ∶ Γ₁ ⇒ᵣ (Γ₂ ▸ (o ∶ τ))
  -- ...
\end{code}}
\begin{code}[hide]
  ⊢idᵣ : ∀ {Γ} → _∶_⇒ᵣ_ {S₁ = S} {S₂ = S} idᵣ Γ Γ
  ⊢extᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {I : Term S₁ (item-of s)} → 
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    --------------------------------------
    extᵣ ρ ∶ Γ₁ ▶ I ⇒ᵣ Γ₂ ▶ ren ρ I
  ⊢dropᵣ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {I : Term S₂ (item-of s)} →
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    -------------
    dropᵣ ρ ∶ Γ₁ ⇒ᵣ Γ₂ ▶ I

⊢wkᵣ : ∀ {I : Term S (item-of s)} → (dropᵣ idᵣ) ∶ Γ ⇒ᵣ (Γ ▶ I)
⊢wkᵣ = ⊢dropᵣ ⊢idᵣ

⊢wk-cstrᵣ : ∀ {o} → idᵣ ∶ Γ ⇒ᵣ (Γ ▸ (o ∶ τ))
⊢wk-cstrᵣ = ⊢drop-cstrᵣ ⊢idᵣ

extᵣidᵣ≡idᵣ : ∀ (x : Var (S ▷ s') s) → extᵣ idᵣ x ≡ idᵣ x
extᵣidᵣ≡idᵣ (here refl) = refl
extᵣidᵣ≡idᵣ (there x) = refl 

⊢ext-ρ₁≡ext-ρ₂ : ∀ {ρ₁ ρ₂ : Ren S₁ S₂} → 
 (∀ {s} (x : Var S₁ s) → ρ₁ x ≡ ρ₂ x) → 
 (∀ {s} (x : Var (S₁ ▷ s') s) → (extᵣ ρ₁) x ≡ (extᵣ ρ₂) x)
⊢ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂ (here refl) = refl
⊢ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂ (there x) = cong there (ρ₁≡ρ₂ x)

ρ₁≡ρ₂→ρ₁τ≡ρ₂τ : ∀ {ρ₁ ρ₂ : Ren S₁ S₂} {τ : Type S₁} → 
  (∀ {s} (x : Var S₁ s) → ρ₁ x ≡ ρ₂ x) → 
  ren ρ₁ τ ≡ ren ρ₂ τ
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ {τ = ` x} ρ₁≡ρ₂ = cong `_ (ρ₁≡ρ₂ x)
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ {τ = `⊤} ρ₁≡ρ₂ = refl
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ {τ = τ₁ ⇒ τ₂} ρ₁≡ρ₂ = cong₂ _⇒_ (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ ρ₁≡ρ₂) (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ ρ₁≡ρ₂)
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ {τ = ∀`α τ} ρ₁≡ρ₂ = cong ∀`α_ (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ (⊢ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂))
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ {τ = [ ` o ∶ τ ]⇒ τ'} ρ₁≡ρ₂ = cong₂ [_]⇒_ (cong₂ _∶_ (cong `_ (ρ₁≡ρ₂ o)) (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ ρ₁≡ρ₂)) (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ ρ₁≡ρ₂) 
\end{code}
\newcommand{\FoRenIdEq}[0]{\begin{code}
idᵣτ≡τ : (τ : Type S) →
  ren idᵣ τ ≡ τ
idᵣτ≡τ (` x) = refl
idᵣτ≡τ `⊤ = refl
idᵣτ≡τ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (idᵣτ≡τ τ₁) (idᵣτ≡τ τ₂)
idᵣτ≡τ (∀`α τ) = cong ∀`α_ (trans (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ extᵣidᵣ≡idᵣ) (idᵣτ≡τ τ))
idᵣτ≡τ ([ ` o ∶ τ ]⇒ τ') = cong₂ [_]⇒_ (cong₂ _∶_ refl (idᵣτ≡τ τ)) (idᵣτ≡τ τ')
\end{code}}
\begin{code}[hide]
-- Substitution Typing ------------------------------------------------------------------


infix 3 _∶_⇒ₛ_
\end{code}
\newcommand{\FoSubTyping}[0]{\begin{code}
data _∶_⇒ₛ_ : Sub S₁ S₂ → Ctx S₁ → Ctx S₂ -> Set where
  ⊢idₛ : ∀ {Γ} → _∶_⇒ₛ_ {S₁ = S} {S₂ = S} idₛ Γ Γ
  ⊢extₛ  : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {I : Term S₁ (item-of s)} → 
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    ----------------------------------
    extₛ σ ∶ Γ₁ ▶ I ⇒ₛ Γ₂ ▶ sub σ I
  ⊢dropₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {I : Term S₂ (item-of s)} →
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    -------------------------
    dropₛ σ ∶ Γ₁ ⇒ₛ (Γ₂ ▶ I) 
  ⊢single-typeₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ : Type S₂} →
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    --------------
    single-typeₛ σ τ ∶ Γ₁ ▶ ⋆ ⇒ₛ Γ₂ 
  ⊢ext-cstrₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} → 
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    --------------------------------------
    σ ∶ (Γ₁ ▸ (o ∶ τ)) ⇒ₛ (Γ₂ ▸ (sub σ o ∶ sub σ τ))
  ⊢drop-cstrₛ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {τ} {o} →
    σ ∶ Γ₁ ⇒ₛ Γ₂ →
    -------------
    σ ∶ Γ₁ ⇒ₛ (Γ₂ ▸ (o ∶ τ)) 
\end{code}}
\begin{code}[hide]
⊢single-typeₛ : single-typeₛ idₛ τ ∶ (Γ ▶ ⋆)  ⇒ₛ Γ
⊢single-typeₛ = ⊢single-typeₛ ⊢idₛ
\end{code}
