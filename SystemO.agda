open import Common using (_▷_; _▷▷_)
open import Data.List using (List; []; _∷_; drop; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)

module SystemO where

-- Sorts --------------------------------------------------------------------------------

data Ctxable : Set where
  ⊤ᶜ : Ctxable
  ⊥ᶜ : Ctxable

data Sort : Ctxable → Set where
  eₛ  : Sort ⊤ᶜ
  oₛ  : Sort ⊤ᶜ 
  cₛ  : Sort ⊥ᶜ
  σₛ  : Sort ⊥ᶜ 
  τₛ  : Sort ⊤ᶜ

Sorts : Set
Sorts = List (Sort ⊤ᶜ)

variable
  r r' r'' r₁ r₂ : Ctxable
  s s' s'' s₁ s₂ : Sort r 
  S S' S'' S₁ S₂ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  o o' o'' o₁ o₂ : oₛ ∈ S
  α α' α'' α₁ α₂ : τₛ ∈ S

Var : Sorts → Sort ⊤ᶜ → Set
Var S s = s ∈ S

OVar : Sorts → Set
OVar S = oₛ ∈ S
  
-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ `let`x=_`in_ ∀`α_⇒_ inst`_∶_`=_`in_
infixr 5 _⇒_ _·_ _∶α→_
infix  6 `_ ↑ₚ_ decl`o`in_

mutual 
  data Term : Sorts → Sort r → Set where
    `_                 : Var S s → Term S s
    λ`x→_              : Term (S ▷ eₛ) eₛ → Term S eₛ
    _·_                : Term S eₛ → Term S eₛ → Term S eₛ
    `let`x=_`in_       : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
    inst`_∶_`=_`in_    : Term S oₛ → Term S σₛ → Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
    decl`o`in_         : Term (S ▷ oₛ) eₛ → Term S eₛ
    _⇒_                : Term S τₛ → Term S τₛ → Term S τₛ
    {-    ε               : Term S cₛ -}
    _∶α→_              : Term S oₛ → Term (S ▷ τₛ) τₛ → Term S cₛ
    {- _,_                : Term S cₛ → Term S cₛ → Term S cₛ -}
    ∀`α_⇒_             : Term S cₛ → Term (S ▷ τₛ) σₛ → Term S σₛ
    ↑ₚ_                : Term S τₛ → Term S σₛ

Expr : Sorts → Set
Expr S = Term S eₛ
Over : Sorts → Set
Over S = Term S oₛ
Cstr : Sorts → Set
Cstr S = Term S cₛ
Poly : Sorts → Set
Poly S = Term S σₛ
Mono : Sorts → Set
Mono S = Term S τₛ

variable
  t t' t'' t₁ t₂ : Term S s
  e e' e'' e₁ e₂ : Expr S
  c c' c'' c₁ c₂ : Cstr S
  σ σ' σ'' σ₁ σ₂ : Poly S
  τ τ' τ'' τ₁ τ₂ : Mono S

-- Context ------------------------------------------------------------------------------

variable 
  Σ Σ' Σ'' Σ₁ Σ₂ : List (Poly S × eₛ ∈ S)

∅ᶜ : List (Poly S × eₛ ∈ S)
∅ᶜ = []

Stores : Sorts → Sort ⊤ᶜ → Set
Stores S eₛ = Poly S
Stores S oₛ = List (Poly S × eₛ ∈ S)
Stores S τₛ = ⊤

depth : ∀ {S s} → Var S s → ℕ
depth (here px) = zero
depth (there x) = suc (depth x)

drop-last : ∀ {S s} → Var S s → Sorts → Sorts
drop-last = drop ∘ suc ∘ depth

Ctx : Sorts → Set
Ctx S = ∀ {s} → (v : Var S s) → Stores (drop-last v S) s

variable
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S

infix 30 _▶▶_

postulate
  _▶▶_ : Ctx S → Ctx S' → Ctx (S ▷▷ S')
  {- _▶▶_ {[]} {S' ▷ s'} Γ Γ' x = {!   !}
  _▶▶_ {S ▷ s} {[]} Γ Γ' x = Γ x
  _▶▶_ {S ▷ s} {S' ▷ s'} Γ Γ' x = {!   !} -}

infix 30 _▶_
_▶_ : Ctx S → Stores S s → Ctx (S ▷ s)
(Γ ▶ g) (here refl) = g
(Γ ▶ _) (there x) = Γ x
 
wk-τ : Mono S → Mono (S ▷ s') 
wk-τ (` x) = ` there x
wk-τ (τ₁ ⇒ τ₂) = (wk-τ τ₁ ⇒ wk-τ τ₂) 

{- wk-c ε = ε -}
-- wk-c (` x ∶α→ τ) = (` there x) ∶α→ {!   !}
{- wk-c (c₁ , c₂) = wk-c c₁ , wk-c c₂ -}

-- see exam
postulate
  wk-c : Cstr S → Cstr (S ▷ s') 
  wk-e : Expr S → Expr (S ▷ s')
  wk-σ : Poly S → Poly (S ▷ s')
{- wk-σ (∀`α c ⇒ σ) = ∀`α {!   !} ⇒ {! wk-σ σ  !}
wk-σ (↑ₚ τ) = ↑ₚ (wk-τ τ) -}

wk-x : Var S s → Var (S ▷ s') s
wk-x t = there t

wkₛ : Stores S s → Stores (S ▷ s') s
wkₛ {s = eₛ} σ = wk-σ σ
wkₛ {s = oₛ} [] = []
wkₛ {s = oₛ} (Σ ▷ (σ , i)) = wkₛ Σ ▷ (wk-σ σ , there i)
wkₛ {s = τₛ} _ = tt  
{- wkₛ {s = iₛ} σ = wk-σ σ -}

wk-drop : (v : Var S s) → Stores (drop-last v S) s → Stores S s
wk-drop (here refl) t = wkₛ t
wk-drop (there x) t = wkₛ (wk-drop x t)

wk-ctx : Ctx S → Var S s → Stores S s 
wk-ctx Γ x = wk-drop x (Γ x)

ctx-drop : Ctx (S ▷ s) → Ctx S
ctx-drop Γ (here refl) = Γ (there (here refl))
ctx-drop Γ (there x) = ctx-drop (λ v → Γ (there v)) x

postulate
  _[_]⊎_ : Ctx S → (o : OVar S) → Poly S → Ctx S

  {- (Γ [ here refl ]⊎ σ) (here refl) = {!    !}
  (Γ [ _ ]⊎ σ) x = Γ x -}

{- cstr-ext : Term S cₛ → Sorts -}
{- cstr-ext' ε = [] -}
{- cstr-ext (o ∶α→ τ) = [] ▷ iₛ -}
{- cstr-ext' (c₁ , c₂) = cstr-ext' c₁ ▷▷ cstr-ext' c₂  -}


{- cstr-ext : Term S σₛ → Sorts
cstr-ext {S} (∀`α c ⇒ σ) = cstr-ext σ ▷▷ cstr-ext' c
cstr-ext {S} (↑ₚ τ) = [] -}

-- Γ ▶ᶜ (` o ∶α→ τ) = Γ [ o ]⊎ (↑ₚ τ)  -- todo α→ τ
  {- Γ ▶ᶜ ε = Γ 
  Γ ▶ᶜ (` o ∶α→ τ) = (Γ [ o ]⊎ (↑ₚ τ)) ▶ (↑ₚ τ)
  Γ ▶ᶜ (c₁ , c₂) = {!   !} -}

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
ren ρ (inst` o ∶ σ `= e₂ `in e₁) = inst` (ren ρ o) ∶ ren ρ σ `=  ren ρ e₂ `in ren (extᵣ ρ) e₁
ren ρ (decl`o`in e) = decl`o`in ren (extᵣ ρ) e
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
{- ren ρ ε = ε -}
ren ρ (o ∶α→ σ) = ren ρ o ∶α→ ren (extᵣ ρ) σ
{- ren ρ (c₁ , c₂) = (ren ρ c₁ , ren ρ c₂) -}
ren ρ (↑ₚ τ) = ↑ₚ ren ρ τ
ren ρ (∀`α cs ⇒ σ) = ∀`α ren ρ cs ⇒ ren (extᵣ ρ) σ

wkᵣ : Ren S (S ▷ s) 
wkᵣ = there

-- Substitution -------------------------------------------------------------------------

takes : Sort r → Sort ⊤ᶜ 
takes eₛ = eₛ
takes σₛ = τₛ
takes τₛ = τₛ 
takes oₛ = eₛ -- never substituted into
takes cₛ = τₛ 
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
sub ξ (inst` o ∶ σ `= e₂ `in e₁) = inst` sub ξ o ∶ sub ξ σ `= sub ξ e₂ `in sub (extₛ ξ) e₁ 
sub ξ (decl`o`in e) = decl`o`in sub (extₛ ξ) e
sub ξ (τ₁ ⇒ τ₂) = sub ξ τ₁ ⇒ sub ξ τ₂
{- sub ξ ε = ε -}
sub ξ (o ∶α→ τ) = sub ξ o ∶α→ sub (extₛ ξ) τ
{- sub ξ (c₁ , c₂) = sub ξ c₁ , sub ξ c₂ -}
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

postulate
  Unique : Ctx S → (o : OVar S) → Poly S → Set
  {- Unique ctx' o σ with wk-ctx ctx' o 
  ... | ctx = ∀ {σ'} → σ' ∈ ctx → {!   !} -}

{- 
Types : Term S s → Set
Types {S = S} {s = eₛ} _ = Poly S
Types {S = S} {s = oₛ} _ = Poly S
Types {S = S} {s = cₛ} _ = Expr S
Types {s = σₛ} _ = ⊤
Types {s = τₛ} _ = ⊤

variable
  T T' T'' T₁ T₂ : Types t
-}

infixr 3 _⊢_∶_
data _⊢_∶_ : Ctx S → Expr S → Poly S → Set where
  ⊢-`x :  
    wk-ctx Γ x ≡ σ →
    ----------------
    Γ ⊢ ` x ∶ σ
  ⊢-`o :
    (σ , x) ∈ (wk-ctx Γ o) →
    ------------------------
    Γ ⊢ ` x ∶ σ
  ⊢-λ : 
    Γ ▶ (↑ₚ τ₁) ⊢ e ∶ ↑ₚ (wk-τ τ₂) →  
    ---------------------------
    Γ ⊢ λ`x→ e ∶ ↑ₚ (τ₁ ⇒ τ₂)
  ⊢-· : 
    Γ ⊢ e₁ ∶ ↑ₚ (τ₁ ⇒ τ₂) →
    Γ ⊢ e₂ ∶ ↑ₚ τ₁ →
    -----------------------
    Γ ⊢ e₁ · e₂ ∶ ↑ₚ τ₂
  ⊢-let : 
    Γ ⊢ e₂ ∶ σ →
    Γ ▶ σ ⊢ e₁ ∶ ↑ₚ (wk-τ τ) →
    ----------------------------
    Γ ⊢ `let`x= e₂ `in e₁ ∶ ↑ₚ τ
  ⊢-decl : 
    Γ ▶ ∅ᶜ ⊢ e ∶ ↑ₚ (wk-τ τ) → 
    ---------------------
    Γ ⊢ decl`o`in e ∶ ↑ₚ τ
  ⊢-inst :
    Unique Γ o σ →
    Γ ⊢ e₂ ∶ σ →
    (Γ [ o ]⊎ σ) ▶ σ ⊢ e₁ ∶ ↑ₚ (wk-τ τ) →  
    ---------------------------------
    Γ ⊢ inst` ` o ∶ σ `= e₂ `in e₁ ∶ ↑ₚ τ
  ⊢-[τ] :
    Γ ⊢ e ∶ ∀`α (` o ∶α→ τ') ⇒ σ →
    (↑ₚ (τ ⇒ τ' [ τ ]) , x) ∈ (wk-ctx Γ o) →
    --------------------------------------------------
    Γ ⊢ e ∶ σ [ τ ]
  ⊢-∀α :
    ((Γ ▶ tt) [ wk-x o ]⊎ (↑ₚ (` here refl ⇒ τ'))) 
        ▶ (↑ₚ (` here refl ⇒ τ')) 
      ⊢ wk-e (wk-e e) ∶ wk-σ σ → 
    ------------------------------------------------------------------------
    Γ ⊢ e ∶ ∀`α (` o ∶α→ τ') ⇒ σ
  {- ⊢-c : 
    (↑ₚ τ , v) ∈ (wk-ctx Γ o) → -- todo α→ τ
    ----------------
    Γ ⊢ (` o ∶α→ τ) ∶ ` v -}
  {- ⊢-∀α : 
    (Γ ▶ᶜ c) ⊢ e ∶ σ →  -}
    ------------------
    -- Γ ⊢ e ∶ ∀`α c ⇒ {! wk-multiple-σ σ  !}
  {- ⊢-ε :
    ----------
    Γ ⊢ ε ∶ tt -}
  {- ⊢-set : 
    Γ ⊢ c₁ ∶ tt →
    Γ ⊢ c₂ ∶ tt →
    ----------------
    Γ ⊢ c₁ , c₂ ∶ tt  -}
  {- ⊢-c : 
    Γ ⊢ ` o ∶ ↑ₚ τ → 
    ----------------
    Γ ⊢ (` o ∶α→ τ) ∶ tt
  ⊢-∀ : 
    Γ ▶ tt ⊢ σ ∶ tt → 
    Γ ▶ tt ⊢ c ∶ tt →
    ------------------
    Γ ⊢ ∀`α c ⇒ σ ∶ tt
  ⊢-τ : 
    ----------
    Γ ⊢ τ ∶ tt -}         