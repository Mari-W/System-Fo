-- [latex] prefix(F)
-- [latex] hide
{-# OPTIONS --allow-unsolved-metas #-}
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)
open import Function using (id; _∘_)
open ≡-Reasoning

module SystemF where

-- Sorts --------------------------------------------------------------------------------

data Bindable : Set where
  ⊤ᴮ : Bindable
  ⊥ᴮ : Bindable

-- [latex] block(Sort)

data Sort : Bindable → Set where
  eₛ  : Sort ⊤ᴮ
  τₛ  : Sort ⊤ᴮ
  κₛ  : Sort ⊥ᴮ
-- [latex] hide
Sorts : Set
-- [latex] inline(Sorts)
Sorts = List (Sort ⊤ᴮ)
-- [latex] hide

infix 25 _▷_ _▷▷_
pattern _▷_ xs x = x ∷ xs
_▷▷_ : {A : Set} → List A → List A → List A
xs ▷▷ ys = ys ++ xs

variable
  r r' r'' r₁ r₂ : Bindable
  s s' s'' s₁ s₂ : Sort r
  S S' S'' S₁ S₂ S₃ : Sorts
  x x' x'' x₁ x₂ : eₛ ∈ S
  α α' α'' α₁ α₂ : τₛ ∈ S

-- Syntax -------------------------------------------------------------------------------

infixr 4 λ`x→_ Λ`α→_ let`x=_`in_ ∀`α_
infixr 5 _⇒_ _·_ _•_
infix  6 `_ 

-- [latex] block(Term)

data Term : Sorts → Sort r → Set where
  `_           : s ∈ S → Term S s
  tt           : Term S eₛ
  λ`x→_        : Term (S ▷ eₛ) eₛ → Term S eₛ
  Λ`α→_        : Term (S ▷ τₛ) eₛ → Term S eₛ
  _·_          : Term S eₛ → Term S eₛ → Term S eₛ
  _•_          : Term S eₛ → Term S τₛ → Term S eₛ
  let`x=_`in_  : Term S eₛ → Term (S ▷ eₛ) eₛ → Term S eₛ
  `⊤           : Term S τₛ
  _⇒_          : Term S τₛ → Term S τₛ → Term S τₛ
  ∀`α_         : Term (S ▷ τₛ) τₛ → Term S τₛ
  ⋆            : Term S κₛ

-- [latex] hide
Var : Sorts → Sort ⊤ᴮ → Set
-- [latex] inline(Var)
Var S s = s ∈ S 

-- [latex] hide
Expr : Sorts → Set
-- [latex] inline(Expr)
Expr S = Term S eₛ

-- [latex] hide
Type : Sorts → Set
-- [latex] inline(Type)
Type S = Term S τₛ

-- [latex] hide

variable
  t t' t'' t₁ t₂ : Term S s
  e e' e'' e₁ e₂ : Expr S
  τ τ' τ'' τ₁ τ₂ : Type S

-- Renaming -----------------------------------------------------------------------------

-- [latex] block(Ren)

Ren : Sorts → Sorts → Set
Ren S₁ S₂ = ∀ s → Var S₁ s → Var S₂ s

-- [latex] hide

idᵣ : Ren S S
idᵣ _ = id

-- [latex] block(renwk)
wkᵣ : Ren S (S ▷ s) 
wkᵣ _ = there

-- [latex] block(renext)
extᵣ : Ren S₁ S₂ → (s : Sort ⊤ᴮ) → Ren (S₁ ▷ s) (S₂ ▷ s)
extᵣ ρ _ _ (here refl) = here refl
extᵣ ρ _ _ (there x) = there (ρ _ x)
-- [latex] hide

dropᵣ : Ren S₁ S₂ → Ren S₁ (S₂ ▷ s) 
dropᵣ ρ _ x = there (ρ _ x)

-- [latex] block(ren)

ren : Ren S₁ S₂ → (Term S₁ s → Term S₂ s)
ren ρ (` x) = ` (ρ _ x)
ren ρ (λ`x→ e) = λ`x→ (ren (extᵣ ρ _) e)
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
-- ...
-- [latex] hide 
ren ρ tt = tt
ren ρ (Λ`α→ e) = Λ`α→ (ren (extᵣ ρ _) e)
ren ρ (e₁ · e₂) = (ren ρ e₁) · (ren ρ e₂)
ren ρ (e • τ) = (ren ρ e) • (ren ρ τ)
ren ρ (let`x= e₂ `in e₁) = let`x= (ren ρ e₂) `in ren (extᵣ ρ _) e₁
ren ρ `⊤ = `⊤
ren ρ (∀`α τ) = ∀`α (ren (extᵣ ρ _) τ)
ren ρ ⋆ = ⋆

-- [latex] block(wk)

wk : Term S s → Term (S ▷ s') s
wk = ren wkᵣ  

-- [latex] hide

variable
  ρ ρ' ρ'' ρ₁ ρ₂ : Ren S₁ S₂

-- Substitution -------------------------------------------------------------------------

-- [latex] block(Sub)

Sub : Sorts → Sorts → Set
Sub S₁ S₂ = ∀ s → Var S₁ s → Term S₂ s

-- [latex] inline(idsub)
idₛ : Sub S S
-- [latex] hide
idₛ s = `_


-- [latex] block(ext)
extₛ : Sub S₁ S₂ → (s : Sort ⊤ᴮ) →  Sub (S₁ ▷ s) (S₂ ▷ s)
extₛ σ s _ (here refl) = ` here refl
extₛ σ s _ (there x) = wk (σ _ x)
-- [latex] hide

dropₛ : Sub S₁ S₂ → Sub S₁ (S₂ ▷ s) 
dropₛ σ _ x = wk (σ _ x)

-- [latex] inline(singlesub)
singleₛ : Sub S₁ S₂ → Term S₂ s → Sub (S₁ ▷ s) S₂
-- [latex] hide
singleₛ σ t _ (here refl) = t
singleₛ σ t _ (there x) = σ _ x

-- [latex] inline(sub)
sub : Sub S₁ S₂ → (Term S₁ s → Term S₂ s)
-- [latex] hide
sub σ (` x) = (σ _ x)
sub σ tt = tt
sub σ (λ`x→ e) = λ`x→ (sub (extₛ σ _) e)
sub σ (Λ`α→ e) = Λ`α→ (sub (extₛ σ _) e)
sub σ (e₁ · e₂) = sub σ e₁ · sub σ e₂
sub σ (e • τ) = sub σ e • sub σ τ
sub σ (let`x= e₂ `in e₁) = let`x= sub σ e₂ `in (sub (extₛ σ _) e₁)
sub σ `⊤ = `⊤
sub σ (τ₁ ⇒ τ₂) = sub σ τ₁ ⇒ sub σ τ₂
sub σ (∀`α τ) = ∀`α (sub (extₛ σ _) τ)
sub σ ⋆ = ⋆

-- [latex] block(subs)

_[_] : Term (S ▷ s') s → Term S s' → Term S s
t [ t' ] = sub (singleₛ idₛ t') t

-- [latex] block(hide)

variable
  σ σ' σ'' σ₁ σ₂ : Sub S₁ S₂ 

-- Context ------------------------------------------------------------------------------

kind-Bindable : Sort ⊤ᴮ → Bindable
kind-Bindable eₛ = ⊤ᴮ
kind-Bindable τₛ = ⊥ᴮ

type-of : (s : Sort ⊤ᴮ) → Sort (kind-Bindable s)
-- [latex] block(kind)
type-of eₛ = τₛ
type-of τₛ = κₛ

-- [latex] hide

variable 
  T T' T'' T₁ T₂ : Term S (type-of s)

-- [latex] block(Ctx)

data Ctx : Sorts → Set where
  ∅   : Ctx []
  _▶_ : Ctx S → Term S (type-of s) → Ctx (S ▷ s)

-- [latex] block(lookup)
lookup : Ctx S → Var S s → Term S (type-of s) 
lookup (Γ ▶ T) (here refl) = wk T
lookup (Γ ▶ T) (there x) = wk (lookup Γ x)
-- [latex] hide

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ : Ctx S

-- Typing -------------------------------------------------------------------------------

-- Expression Typing

infix 3 _⊢_∶_
-- [latex] block(Typing)
data _⊢_∶_ : Ctx S → Term S s → Term S (type-of s) → Set where
  ⊢`x :  
    lookup Γ x ≡ τ →
    Γ ⊢ ` x ∶ τ
  ⊢⊤ : 
    Γ ⊢ tt ∶ `⊤
  ⊢λ : 
    Γ ▶ τ ⊢ e ∶ wk τ' →  
    Γ ⊢ λ`x→ e ∶ τ ⇒ τ' 
  ⊢Λ : 
    Γ ▶ ⋆ ⊢ e ∶ τ →  
    Γ ⊢ Λ`α→ e ∶ ∀`α τ
  ⊢· : 
    Γ ⊢ e₁ ∶ τ₁ ⇒ τ₂ →
    Γ ⊢ e₂ ∶ τ₁ →
    Γ ⊢ e₁ · e₂ ∶ τ₂
  ⊢• : 
    Γ ⊢ e ∶ ∀`α τ →
    Γ ⊢ e • τ' ∶ τ [ τ' ]
  ⊢let : 
    Γ ⊢ e₂ ∶ τ →
    Γ ▶ τ ⊢ e₁ ∶ wk τ' →
    Γ ⊢ let`x= e₂ `in e₁ ∶ τ'
  ⊢τ :
    Γ ⊢ τ ∶ ⋆

-- [latex] hide

-- Renaming Typing

infix 3 _∶_⇒ᵣ_
-- [latex] block(RenTyping)
data _∶_⇒ᵣ_ : Ren S₁ S₂ → Ctx S₁ → Ctx S₂ → Set where
  ⊢idᵣ : ∀ {Γ} → _∶_⇒ᵣ_ {S₁ = S} {S₂ = S} idᵣ Γ Γ
  ⊢extᵣ : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} 
            {T' : Term S₁ (type-of s)} → 
    ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
    (extᵣ ρ _) ∶ (Γ₁ ▶ T') ⇒ᵣ (Γ₂ ▶ ren ρ T')
  ⊢dropᵣ : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} 
             {T' : Term S₂ (type-of s)} →
    ρ ∶ Γ₁  ⇒ᵣ Γ₂ →
    (dropᵣ ρ) ∶ Γ₁ ⇒ᵣ (Γ₂ ▶ T')

-- [latex] hide

⊢wkᵣ : ∀ {T : Term S (type-of s)} → (dropᵣ idᵣ) ∶ Γ ⇒ᵣ (Γ ▶ T)
⊢wkᵣ = ⊢dropᵣ ⊢idᵣ


-- [latex] block(SubTyping)

_∶_⇒ₛ_ : Sub S₁ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_⇒ₛ_ {S₁ = S₁} σ Γ₁ Γ₂ = ∀ {s} (x : Var S₁ s) → 
                           Γ₂ ⊢ σ _ x ∶ (sub σ (lookup Γ₁ x))

-- [latex] hide

-- Semantics ----------------------------------------------------------------------------

-- [latex] block(Val)

data Val : Expr S → Set where
  v-λ : Val (λ`x→ e)
  v-Λ : Val (Λ`α→ e)
  v-tt : ∀ {S} → Val (tt {S = S})

-- [latex] hide

infixr 3 _↪_
-- [latex] block(Semantics)
data _↪_ : Expr S → Expr S → Set where
  β-λ :
    Val e₂ →
    (λ`x→ e₁) · e₂ ↪ e₁ [ e₂ ]
  β-Λ :
    (Λ`α→ e) • τ ↪ e [ τ ]
  β-let : 
    Val e₂ →
    let`x= e₂ `in e₁ ↪ (e₁ [ e₂ ])
  ξ-·₁ :
    e₁ ↪ e →
    e₁ · e₂ ↪ e · e₂
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    e₁ · e₂ ↪ e₁ · e
  ξ-• :
    e ↪ e' →
    e • τ ↪ e' • τ
  ξ-let :
    e₂ ↪ e →
    let`x= e₂ `in e₁ ↪ let`x= e `in e₁ 

-- [latex] hide

-- Soundness ---------------------------------------------------------------------------- 

-- Progress

-- [latex] block(Progress)

progress : 
  ∅ ⊢ e ∶ τ →
  (∃[ e' ] (e ↪ e')) ⊎ Val e
progress ⊢⊤ = inj₂ v-tt
progress (⊢λ _) = inj₂ v-λ
progress (⊢Λ _) = inj₂ v-Λ
progress (⊢· {e₁ = e₁} {e₂ = e₂} ⊢e₁  ⊢e₂) with progress ⊢e₁ | progress ⊢e₂ 
... | inj₁ (e₁' , e₁↪e₁') | _ = inj₁ (e₁' · e₂ , ξ-·₁ e₁↪e₁')
... | inj₂ v | inj₁ (e₂' , e₂↪e₂') = inj₁ (e₁ · e₂' , ξ-·₂ e₂↪e₂' v)
... | inj₂ (v-λ {e = e₁}) | inj₂ v = inj₁ (e₁ [ e₂ ] , β-λ v)
progress (⊢• {τ' = τ'} ⊢e) with progress ⊢e 
... | inj₁ (e' , e↪e') = inj₁ (e' • τ' , ξ-• e↪e')
... | inj₂ (v-Λ {e = e}) = inj₁ (e [ τ' ] , β-Λ)
progress (⊢let  {e₂ = e₂} {e₁ = e₁} ⊢e₂ ⊢e₁) with progress ⊢e₂ 
... | inj₁ (e₂' , e₂↪e₂') = inj₁ ((let`x= e₂' `in e₁) , ξ-let e₂↪e₂')
... | inj₂ v = inj₁ (e₁ [ e₂ ] , β-let v)

-- [latex] hide

-- Subject Reduction

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C      : Set ℓ

postulate
  fun-ext : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x} →
    (∀ (x : A) → f x ≡ g x) →
    f ≡ g

fun-ext₂ : ∀ {A₁ : Set ℓ₁} {A₂ : A₁ → Set ℓ₂} {B : (x : A₁) → A₂ x → Set ℓ₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y


_ρσ→σ_ : Ren S₁ S₂ → Sub S₂ S₃ → Sub S₁ S₃
(ρ ρσ→σ σ) _ x = σ _ (ρ _ x)

_ρρ→ρ_ : Ren S₁ S₂ → Ren S₂ S₃ → Ren S₁ S₃
(ρ₁ ρρ→ρ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_σρ→σ_ : Sub S₁ S₂ → Ren S₂ S₃ → Sub S₁ S₃
(σ σρ→σ ρ) _ x = ren ρ (σ _ x)

_σσ→σ_ : Sub S₁ S₂ → Sub S₂ S₃ → Sub S₁ S₃
(σ₁ σσ→σ σ₂) _ x = sub σ₂ (σ₁ _ x)

extᵣidᵣ≡idᵣ : ∀ (x : Var (S ▷ s') s) → extᵣ idᵣ _ _ x ≡ idᵣ _ x
extᵣidᵣ≡idᵣ (here refl) = refl
extᵣidᵣ≡idᵣ (there x) = refl 

ρ₁≡ρ₂→ext-ρ₁≡ext-ρ₂ : ∀ {ρ₁ ρ₂ : Ren S₁ S₂} → 
 (∀ {s} (x : Var S₁ s) → ρ₁ _ x ≡ ρ₂ _ x) → 
 (∀ {s} (x : Var (S₁ ▷ s') s) → (extᵣ ρ₁ _) _ x ≡ (extᵣ ρ₂ _) _ x)
ρ₁≡ρ₂→ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂ (here refl) = refl
ρ₁≡ρ₂→ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂ (there x) = cong there (ρ₁≡ρ₂ x)

ρ₁≡ρ₂→ρ₁τ≡ρ₂τ : ∀ {ρ₁ ρ₂ : Ren S₁ S₂} (τ : Type S₁) → 
  (∀ {s} (x : Var S₁ s) → ρ₁ _ x ≡ ρ₂ _ x) → 
  ren ρ₁ τ ≡ ren ρ₂ τ
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ (` x) ρ₁≡ρ₂ = cong `_ (ρ₁≡ρ₂ x)
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ `⊤ ρ₁≡ρ₂ = refl
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ (τ₁ ⇒ τ₂) ρ₁≡ρ₂ = cong₂ _⇒_ (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ τ₁ ρ₁≡ρ₂) (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ τ₂ ρ₁≡ρ₂)
ρ₁≡ρ₂→ρ₁τ≡ρ₂τ (∀`α τ) ρ₁≡ρ₂ = cong ∀`α_ (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ τ (ρ₁≡ρ₂→ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂))

idᵣτ≡τ : (τ : Type S) →
  ren idᵣ τ ≡ τ
idᵣτ≡τ (` x) = refl
idᵣτ≡τ `⊤ = refl
idᵣτ≡τ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (idᵣτ≡τ τ₁) (idᵣτ≡τ τ₂)
idᵣτ≡τ (∀`α τ) = cong ∀`α_ (trans (ρ₁≡ρ₂→ρ₁τ≡ρ₂τ τ extᵣidᵣ≡idᵣ) (idᵣτ≡τ τ))

extₛidₛ≡idₛ : ∀ (x : Var (S ▷ s') s) → extₛ idₛ _ _ x ≡ idₛ _ x
extₛidₛ≡idₛ (here refl) = refl
extₛidₛ≡idₛ (there x) = refl 

σ₁≡σ₂→ext-σ₁≡ext-σ₂ : ∀ {σ₁ σ₂ : Sub S₁ S₂} → 
 (∀ {s} (x : Var S₁ s) → σ₁ _ x ≡ σ₂ _ x) → 
 (∀ {s} (x : Var (S₁ ▷ s') s) → (extₛ σ₁ _) _ x ≡ (extₛ σ₂ _) _ x)
σ₁≡σ₂→ext-σ₁≡ext-σ₂ σ₁≡σ₂ (here refl) = refl
σ₁≡σ₂→ext-σ₁≡ext-σ₂ σ₁≡σ₂ (there x) = cong wk (σ₁≡σ₂ x)

σ₁≡σ₂→σ₁t≡σ₂t : ∀ {σ₁ σ₂ : Sub S₁ S₂} (t : Term S₁ s) → 
  (∀ {s} (x : Var S₁ s) → σ₁ _ x ≡ σ₂ _ x) → 
  sub σ₁ t ≡ sub σ₂ t
σ₁≡σ₂→σ₁t≡σ₂t (` x) σ₁≡σ₂ = σ₁≡σ₂ x
σ₁≡σ₂→σ₁t≡σ₂t `⊤ σ₁≡σ₂ = refl
σ₁≡σ₂→σ₁t≡σ₂t (τ₁ ⇒ τ₂) σ₁≡σ₂ = cong₂ _⇒_ (σ₁≡σ₂→σ₁t≡σ₂t τ₁ σ₁≡σ₂) (σ₁≡σ₂→σ₁t≡σ₂t τ₂ σ₁≡σ₂)
σ₁≡σ₂→σ₁t≡σ₂t (∀`α τ) σ₁≡σ₂ = cong ∀`α_ (σ₁≡σ₂→σ₁t≡σ₂t τ (σ₁≡σ₂→ext-σ₁≡ext-σ₂ σ₁≡σ₂))
σ₁≡σ₂→σ₁t≡σ₂t tt σ₁≡σ₂ = refl
σ₁≡σ₂→σ₁t≡σ₂t (λ`x→ e) σ₁≡σ₂ = cong λ`x→_ (σ₁≡σ₂→σ₁t≡σ₂t e (σ₁≡σ₂→ext-σ₁≡ext-σ₂ σ₁≡σ₂))
σ₁≡σ₂→σ₁t≡σ₂t (Λ`α→ e) σ₁≡σ₂ = cong Λ`α→_ (σ₁≡σ₂→σ₁t≡σ₂t e (σ₁≡σ₂→ext-σ₁≡ext-σ₂ σ₁≡σ₂))
σ₁≡σ₂→σ₁t≡σ₂t (e₁ · e₂) σ₁≡σ₂ = cong₂ _·_ (σ₁≡σ₂→σ₁t≡σ₂t e₁ σ₁≡σ₂) (σ₁≡σ₂→σ₁t≡σ₂t e₂ σ₁≡σ₂)
σ₁≡σ₂→σ₁t≡σ₂t (e • τ) σ₁≡σ₂ = cong₂ _•_ (σ₁≡σ₂→σ₁t≡σ₂t e σ₁≡σ₂) (σ₁≡σ₂→σ₁t≡σ₂t τ σ₁≡σ₂)
σ₁≡σ₂→σ₁t≡σ₂t (let`x= e₂ `in e₁) σ₁≡σ₂ = cong₂ let`x=_`in_ (σ₁≡σ₂→σ₁t≡σ₂t e₂ σ₁≡σ₂) (σ₁≡σ₂→σ₁t≡σ₂t e₁(σ₁≡σ₂→ext-σ₁≡ext-σ₂ σ₁≡σ₂))
σ₁≡σ₂→σ₁t≡σ₂t ⋆ σ₁≡σ₂ = refl

idₛt≡t : (t : Term S s) →
  sub idₛ t ≡ t
idₛt≡t (` x) = refl
idₛt≡t `⊤ = refl
idₛt≡t (τ₁ ⇒ τ₂) = cong₂ _⇒_ (idₛt≡t τ₁) (idₛt≡t τ₂)
idₛt≡t (∀`α τ) = cong ∀`α_ (trans (σ₁≡σ₂→σ₁t≡σ₂t τ extₛidₛ≡idₛ) (idₛt≡t τ))
idₛt≡t tt = refl
idₛt≡t (λ`x→ e) = cong λ`x→_ (trans (σ₁≡σ₂→σ₁t≡σ₂t e extₛidₛ≡idₛ) (idₛt≡t e))
idₛt≡t (Λ`α→ e) = cong Λ`α→_ (trans (σ₁≡σ₂→σ₁t≡σ₂t e extₛidₛ≡idₛ) (idₛt≡t e))
idₛt≡t (e₁ · e₂) = cong₂ _·_ (idₛt≡t e₁) (idₛt≡t e₂)
idₛt≡t (e • τ) = cong₂ _•_ (idₛt≡t e) (idₛt≡t τ)
idₛt≡t (let`x= e₂ `in e₁) = cong₂ let`x=_`in_ (idₛt≡t e₂) (trans (σ₁≡σ₂→σ₁t≡σ₂t e₁ extₛidₛ≡idₛ) (idₛt≡t e₁))
idₛt≡t ⋆ = refl

⊢idₛ : ∀ {Γ : Ctx S} {t : Term S s} {T : Term S (type-of s)} (⊢t : Γ ⊢ t ∶ T) → idₛ ∶ Γ ⇒ₛ Γ
⊢idₛ {Γ = Γ} ⊢t {eₛ} x = ⊢`x (sym (idₛt≡t (lookup Γ x)))
⊢idₛ {Γ = Γ} ⊢t {τₛ} x with lookup Γ x
... | ⋆ = ⊢τ

↑σρ≡↑σ·↑ρ : ∀ s (ρ : Ren S₁ S₂) (σ : Sub S₂ S₃) →
  extₛ (ρ ρσ→σ σ) s ≡ (extᵣ ρ _) ρσ→σ (extₛ σ s)
↑σρ≡↑σ·↑ρ s ρ σ = fun-ext₂ λ { _ (here refl) → refl
                             ; _ (there x) → refl }

mutual 
  ρ↑t·σ≡ρ·σ↑t : ∀ (t : Term (S₁ ▷ s') s) (ρ : Ren S₁ S₂) (σ : Sub S₂ S₃) →
    sub (extₛ σ _) (ren (extᵣ ρ _) t) ≡ sub (extₛ (ρ ρσ→σ σ) _) t
  ρ↑t·σ≡ρ·σ↑t {s' = s'} t ρ σ = begin  
      sub (extₛ σ _) (ren (extᵣ ρ _) t)
    ≡⟨ ρt·σ≡ρ·σt t (extᵣ ρ _) (extₛ σ _) ⟩
      sub (extᵣ ρ _ ρσ→σ extₛ σ _) t
    ≡⟨ cong (λ σ → sub σ t) (sym (↑σρ≡↑σ·↑ρ s' ρ σ)) ⟩
      sub (extₛ (ρ ρσ→σ σ) _) t
    ∎

  ρt·σ≡ρ·σt : ∀ (t : Term S₁ s) (ρ : Ren S₁ S₂) (σ : Sub S₂ S₃) →
    sub σ (ren ρ t) ≡ sub (ρ ρσ→σ σ) t
  ρt·σ≡ρ·σt (` x) ρ σ = refl
  ρt·σ≡ρ·σt tt ρ σ = refl
  ρt·σ≡ρ·σt (λ`x→ e) ρ σ = cong λ`x→_ (ρ↑t·σ≡ρ·σ↑t e ρ σ)
  ρt·σ≡ρ·σt (Λ`α→ e) ρ σ = cong Λ`α→_ (ρ↑t·σ≡ρ·σ↑t e ρ σ)
  ρt·σ≡ρ·σt (e₁ · e₂) ρ σ = cong₂ _·_ (ρt·σ≡ρ·σt e₁ ρ σ) (ρt·σ≡ρ·σt e₂ ρ σ)
  ρt·σ≡ρ·σt (e • τ) ρ σ = cong₂ _•_ (ρt·σ≡ρ·σt e ρ σ) (ρt·σ≡ρ·σt τ ρ σ)
  ρt·σ≡ρ·σt (let`x= e₂ `in e₁) ρ σ = cong₂ let`x=_`in_ (ρt·σ≡ρ·σt e₂ ρ σ) (ρ↑t·σ≡ρ·σ↑t e₁ ρ σ)
  ρt·σ≡ρ·σt `⊤ ρ σ = refl
  ρt·σ≡ρ·σt (τ₁ ⇒ τ₂) ρ σ = cong₂ _⇒_ (ρt·σ≡ρ·σt τ₁ ρ σ) (ρt·σ≡ρ·σt τ₂ ρ σ)
  ρt·σ≡ρ·σt (∀`α τ) ρ σ = cong ∀`α_ (ρ↑t·σ≡ρ·σ↑t τ ρ σ)
  ρt·σ≡ρ·σt ⋆ ρ σ = refl 

↑ρρ≡↑ρ·↑ρ : ∀ s (ρ₁ : Ren S₁ S₂) (ρ₂ : Ren S₂ S₃) →
  extᵣ (ρ₁ ρρ→ρ ρ₂) s ≡ (extᵣ ρ₁ _) ρρ→ρ (extᵣ ρ₂ _)
↑ρρ≡↑ρ·↑ρ s ρ₁ ρ₂ = fun-ext₂ λ { _ (here refl) → refl
                               ; _ (there x) → refl }

mutual 
  ρ↑t·ρ≡ρ·ρ↑t : ∀ (t : Term (S₁ ▷ s') s) (ρ₁ : Ren S₁ S₂) (ρ₂ : Ren S₂ S₃) →
    ren (extᵣ ρ₂ _) (ren (extᵣ ρ₁ _) t) ≡ ren (extᵣ (ρ₁ ρρ→ρ ρ₂) _) t
  ρ↑t·ρ≡ρ·ρ↑t t ρ₁ ρ₂ = begin  
      ren (extᵣ ρ₂ _) (ren (extᵣ ρ₁ _) t)
    ≡⟨ ρt·ρ≡ρ·ρt t (extᵣ ρ₁ _) (extᵣ ρ₂ _) ⟩
      ren (extᵣ ρ₁ _ ρρ→ρ extᵣ ρ₂ _) t
    ≡⟨ cong (λ ρ → ren ρ t) (sym (↑ρρ≡↑ρ·↑ρ _ ρ₁ ρ₂)) ⟩
      ren (extᵣ (ρ₁ ρρ→ρ ρ₂) _) t
    ∎

  ρt·ρ≡ρ·ρt : ∀ (t : Term S₁ s) (ρ₁ : Ren S₁ S₂) (ρ₂ : Ren S₂ S₃) →
    ren ρ₂ (ren ρ₁ t) ≡ ren (ρ₁ ρρ→ρ ρ₂) t
  ρt·ρ≡ρ·ρt (` x) ρ₁ ρ₂ = refl
  ρt·ρ≡ρ·ρt tt ρ₁ ρ₂ = refl
  ρt·ρ≡ρ·ρt (λ`x→ e) ρ₁ ρ₂ = cong λ`x→_ (ρ↑t·ρ≡ρ·ρ↑t e ρ₁ ρ₂)
  ρt·ρ≡ρ·ρt (Λ`α→ e) ρ₁ ρ₂ = cong Λ`α→_ (ρ↑t·ρ≡ρ·ρ↑t e ρ₁ ρ₂)
  ρt·ρ≡ρ·ρt (e₁ · e₂) ρ₁ ρ₂ = cong₂ _·_ (ρt·ρ≡ρ·ρt e₁ ρ₁ ρ₂) (ρt·ρ≡ρ·ρt e₂ ρ₁ ρ₂)
  ρt·ρ≡ρ·ρt (e • τ) ρ₁ ρ₂ = cong₂ _•_ (ρt·ρ≡ρ·ρt e ρ₁ ρ₂) (ρt·ρ≡ρ·ρt τ ρ₁ ρ₂)
  ρt·ρ≡ρ·ρt (let`x= e₂ `in e₁) ρ₁ ρ₂ = cong₂ let`x=_`in_ (ρt·ρ≡ρ·ρt e₂ ρ₁ ρ₂) (ρ↑t·ρ≡ρ·ρ↑t e₁ ρ₁ ρ₂)
  ρt·ρ≡ρ·ρt `⊤ ρ₁ ρ₂ = refl
  ρt·ρ≡ρ·ρt (τ₁ ⇒ τ₂) ρ₁ ρ₂ = cong₂ _⇒_ (ρt·ρ≡ρ·ρt τ₁ ρ₁ ρ₂) (ρt·ρ≡ρ·ρt τ₂ ρ₁ ρ₂)
  ρt·ρ≡ρ·ρt (∀`α τ) ρ₁ ρ₂ = cong ∀`α_ (ρ↑t·ρ≡ρ·ρ↑t τ ρ₁ ρ₂)
  ρt·ρ≡ρ·ρt ⋆ ρ₁ ρ₂ = refl 

↑ρ·wkt≡wk·ρt : ∀ (t : Term S₁ s') (ρ : Ren S₁ S₂) →
  ren (extᵣ ρ s) (wk t) ≡ wk (ren ρ t) 
↑ρ·wkt≡wk·ρt {s = s} t ρ = 
  begin 
    ren (extᵣ ρ s) (ren wkᵣ t)
  ≡⟨ ρt·ρ≡ρ·ρt t wkᵣ (extᵣ ρ s) ⟩
    ren (wkᵣ ρρ→ρ extᵣ ρ s) t
  ≡⟨ sym (ρt·ρ≡ρ·ρt t ρ wkᵣ) ⟩
    ren wkᵣ (ren ρ t)
  ∎

↑ρσ≡↑ρ·↑σ : ∀ s (σ : Sub S₁ S₂) (ρ : Ren S₂ S₃) →
  extₛ (σ σρ→σ ρ) s ≡ (extₛ σ _ σρ→σ extᵣ ρ _)
↑ρσ≡↑ρ·↑σ s σ ρ =  fun-ext₂ λ { _ (here refl) → refl
                              ; _ (there x) →  sym (↑ρ·wkt≡wk·ρt (σ _ x) ρ) } 

mutual 
  σ↑t·ρ≡σ·ρ↑t : ∀ (t : Term (S₁ ▷ s') s) (σ : Sub S₁ S₂) (ρ : Ren S₂ S₃) →
    ren (extᵣ ρ _) (sub (extₛ σ _) t) ≡ sub (extₛ (σ σρ→σ ρ) _) t
  σ↑t·ρ≡σ·ρ↑t {s' = s'} t σ ρ = begin 
      ren (extᵣ ρ _) (sub (extₛ σ s') t)
    ≡⟨ σt·ρ≡σ·ρt t (extₛ σ _) (extᵣ ρ _) ⟩
      sub (extₛ σ s' σρ→σ extᵣ ρ _) t
    ≡⟨ cong (λ σ → sub σ t) (sym (↑ρσ≡↑ρ·↑σ s' σ ρ)) ⟩
      sub (extₛ (σ σρ→σ ρ) s') t
    ∎ 

  σt·ρ≡σ·ρt : ∀ (t : Term S₁ s) (σ : Sub S₁ S₂) (ρ : Ren S₂ S₃) →
    ren ρ (sub σ t) ≡ sub (σ σρ→σ ρ) t
  σt·ρ≡σ·ρt (` x) σ ρ = refl
  σt·ρ≡σ·ρt tt σ ρ = refl
  σt·ρ≡σ·ρt (λ`x→ e) σ ρ = cong λ`x→_ (σ↑t·ρ≡σ·ρ↑t e σ ρ)
  σt·ρ≡σ·ρt (Λ`α→ e) σ ρ = cong Λ`α→_ (σ↑t·ρ≡σ·ρ↑t e σ ρ)
  σt·ρ≡σ·ρt (e₁ · e₂) σ ρ = cong₂ _·_ (σt·ρ≡σ·ρt e₁ σ ρ) (σt·ρ≡σ·ρt e₂ σ ρ)
  σt·ρ≡σ·ρt (e • τ) σ ρ = cong₂ _•_ (σt·ρ≡σ·ρt e σ ρ) (σt·ρ≡σ·ρt τ σ ρ)
  σt·ρ≡σ·ρt (let`x= e₂ `in e₁) σ ρ = cong₂ let`x=_`in_  (σt·ρ≡σ·ρt e₂ σ ρ) (σ↑t·ρ≡σ·ρ↑t e₁ σ ρ)
  σt·ρ≡σ·ρt `⊤ σ ρ = refl
  σt·ρ≡σ·ρt (τ₁ ⇒ τ₂) σ ρ = cong₂ _⇒_ (σt·ρ≡σ·ρt τ₁ σ ρ) (σt·ρ≡σ·ρt τ₂ σ ρ)
  σt·ρ≡σ·ρt (∀`α τ) σ ρ = cong ∀`α_ (σ↑t·ρ≡σ·ρ↑t τ σ ρ)
  σt·ρ≡σ·ρt ⋆ σ ρ = refl

σ↑·wkt≡wk·σt : ∀ s' (σ : Sub S₁ S₂) (t : Term S₁ s) →
  sub (extₛ σ _) (wk {s' = s'} t) ≡ wk (sub σ t)
σ↑·wkt≡wk·σt s' σ t = 
  begin 
    sub (extₛ σ _) (wk t) 
  ≡⟨ ρt·σ≡ρ·σt t wkᵣ (extₛ σ _) ⟩
    sub (σ σρ→σ λ _ → there) t
  ≡⟨ sym (σt·ρ≡σ·ρt t σ wkᵣ) ⟩
    ren wkᵣ (sub σ t)
  ∎

↑σσ≡↑σ·↑σ : ∀ s (σ₁ : Sub S₁ S₂) (σ₂ : Sub S₂ S₃) →
  extₛ (σ₁ σσ→σ σ₂) s ≡ (extₛ σ₁ _ σσ→σ extₛ σ₂ _)
↑σσ≡↑σ·↑σ s σ₁ σ₂ =  fun-ext₂ 
  λ { _ (here refl) → refl
    ; s' (there x) → 
      begin 
        (extₛ (σ₁ σσ→σ σ₂) s) s' (there x) 
      ≡⟨ sym (σ↑·wkt≡wk·σt s σ₂ (σ₁ s' x)) ⟩
        (extₛ σ₁ s σσ→σ extₛ σ₂ s) s' (there x)
      ∎
  } 

mutual 
  σ↑t·σ≡σ·σ↑t : ∀ (t : Term (S₁ ▷ s') s) (σ₁ : Sub S₁ S₂) (σ₂ : Sub S₂ S₃) →
    sub (extₛ σ₂ _) (sub (extₛ σ₁ _) t) ≡ sub (extₛ (σ₁ σσ→σ σ₂) _) t
  σ↑t·σ≡σ·σ↑t {s' = s'} t σ₁ σ₂ = begin 
      sub (extₛ σ₂ _) (sub (extₛ σ₁ _) t)
    ≡⟨ σt·σ≡σ·σt t (extₛ σ₁ _) (extₛ σ₂ _) ⟩
      sub (extₛ σ₁ s' σσ→σ extₛ σ₂ s') t
    ≡⟨ cong (λ σ → sub σ t) (sym (↑σσ≡↑σ·↑σ s' σ₁ σ₂)) ⟩
      sub (extₛ (σ₁ σσ→σ σ₂) s') t
    ∎ 

  σt·σ≡σ·σt : ∀ (t : Term S₁ s) (σ₁ : Sub S₁ S₂) (σ₂ : Sub S₂ S₃) →
    sub σ₂ (sub σ₁ t) ≡ sub (σ₁ σσ→σ σ₂) t
  σt·σ≡σ·σt (` x) σ₁ σ₂ = refl
  σt·σ≡σ·σt tt σ₁ σ₂ = refl
  σt·σ≡σ·σt (λ`x→ e) σ₁ σ₂ = cong λ`x→_ (σ↑t·σ≡σ·σ↑t e σ₁ σ₂)
  σt·σ≡σ·σt (Λ`α→ e) σ₁ σ₂ = cong Λ`α→_ (σ↑t·σ≡σ·σ↑t e σ₁ σ₂)
  σt·σ≡σ·σt (e₁ · e₂) σ₁ σ₂ = cong₂ _·_ (σt·σ≡σ·σt e₁ σ₁ σ₂) (σt·σ≡σ·σt e₂ σ₁ σ₂)
  σt·σ≡σ·σt (e • τ) σ₁ σ₂ = cong₂ _•_ (σt·σ≡σ·σt e σ₁ σ₂) (σt·σ≡σ·σt τ σ₁ σ₂)
  σt·σ≡σ·σt (let`x= e₂ `in e₁) σ₁ σ₂ = cong₂ let`x=_`in_  (σt·σ≡σ·σt e₂ σ₁ σ₂) (σ↑t·σ≡σ·σ↑t e₁ σ₁ σ₂)
  σt·σ≡σ·σt `⊤ σ₁ σ₂ = refl
  σt·σ≡σ·σt (τ₁ ⇒ τ₂) σ₁ σ₂ = cong₂ _⇒_ (σt·σ≡σ·σt τ₁ σ₁ σ₂) (σt·σ≡σ·σt τ₂ σ₁ σ₂)
  σt·σ≡σ·σt (∀`α τ) σ₁ σ₂ = cong ∀`α_ (σ↑t·σ≡σ·σ↑t τ σ₁ σ₂)
  σt·σ≡σ·σt ⋆ σ₁ σ₂ = refl
 

⊢ρ-preserves-Γ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} (x : Var S₁ s) →
  ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
  ren ρ (lookup Γ₁ x) ≡ lookup Γ₂ (ρ _ x)
⊢ρ-preserves-Γ {s = eₛ} {Γ₁ = Γ₁} x ⊢idᵣ = idᵣτ≡τ (lookup Γ₁ x)
⊢ρ-preserves-Γ {s = τₛ} {Γ₁ = Γ₁} x ⊢idᵣ with (lookup Γ₁ x) 
... | ⋆ = refl
⊢ρ-preserves-Γ (here refl) (⊢extᵣ {ρ = ρ} {T' = T'} ⊢ρ) = (↑ρ·wkt≡wk·ρt T' ρ) 
⊢ρ-preserves-Γ (there x) (⊢extᵣ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ) = 
  begin 
    ren (extᵣ ρ _) (wk (lookup Γ₁ x))
  ≡⟨ ↑ρ·wkt≡wk·ρt (lookup Γ₁ x) ρ ⟩
    wk (ren ρ (lookup Γ₁ x))
  ≡⟨ cong wk (⊢ρ-preserves-Γ x ⊢ρ) ⟩
    wk (lookup Γ₂ (ρ _ x))
  ∎
⊢ρ-preserves-Γ x (⊢dropᵣ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ) = 
  begin 
    ren (dropᵣ ρ) (lookup Γ₁ x)
  ≡⟨ sym (ρt·ρ≡ρ·ρt (lookup Γ₁ x) ρ wkᵣ) ⟩
    ren wkᵣ (ren ρ (lookup Γ₁ x))
  ≡⟨ cong wk (⊢ρ-preserves-Γ x ⊢ρ) ⟩
    wk (lookup Γ₂ (ρ _ x))
  ∎

ρ[τ]≡[ρτ]·ρ↑ : ∀ (τ : Type S₁) (ρ : Ren S₁ S₂) →
  ((singleₛ idₛ) τ σρ→σ ρ) ≡ ((extᵣ ρ τₛ) ρσ→σ (singleₛ idₛ (ren ρ τ)))
ρ[τ]≡[ρτ]·ρ↑ T ρ = fun-ext₂ λ { _ (here refl) → refl
                            ; _ (there x) → refl }

ρτ[τ']≡ρτ[ρ↑τ'] : ∀ (ρ : Ren S₁ S₂) (τ : Type (S₁ ▷ τₛ)) (τ' : Type S₁) →
  ren ρ (τ [ τ' ]) ≡ ren (extᵣ ρ _) τ [ ren ρ τ' ]
ρτ[τ']≡ρτ[ρ↑τ'] ρ τ τ' = 
  begin 
    ren ρ (τ [ τ' ])
  ≡⟨ σt·ρ≡σ·ρt τ (singleₛ idₛ τ') ρ ⟩
    sub (singleₛ idₛ τ' σρ→σ ρ) τ
  ≡⟨ cong (λ σ → sub σ τ) (ρ[τ]≡[ρτ]·ρ↑ τ' ρ) ⟩
    sub ((extᵣ ρ τₛ) ρσ→σ (singleₛ idₛ (ren ρ τ'))) τ
  ≡⟨ sym (ρt·σ≡ρ·σt τ (extᵣ ρ τₛ) (singleₛ idₛ (ren ρ τ'))) ⟩
    sub (singleₛ idₛ (ren ρ τ')) (ren (extᵣ ρ τₛ) τ)
  ∎

⊢ρ-preserves : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : Term S₁ s} {T : Term S₁ (type-of s)} →
  ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (ren ρ t) ∶ (ren ρ T)
⊢ρ-preserves ⊢ρ (⊢`x {x = x} refl) = ⊢`x (sym (⊢ρ-preserves-Γ x ⊢ρ))
⊢ρ-preserves ⊢ρ ⊢⊤ = ⊢⊤
⊢ρ-preserves {ρ = ρ} {T = τ₁ ⇒ τ₂} ⊢ρ (⊢λ ⊢e) =  ⊢λ (subst (_ ⊢ _ ∶_) (↑ρ·wkt≡wk·ρt τ₂ ρ) (⊢ρ-preserves (⊢extᵣ ⊢ρ) ⊢e)) 
⊢ρ-preserves ⊢ρ (⊢Λ ⊢e) = ⊢Λ (⊢ρ-preserves (⊢extᵣ ⊢ρ) ⊢e)
⊢ρ-preserves ⊢ρ (⊢· ⊢e₁ ⊢e₂) = ⊢· (⊢ρ-preserves ⊢ρ ⊢e₁) (⊢ρ-preserves ⊢ρ ⊢e₂)
⊢ρ-preserves {ρ = ρ} ⊢ρ (⊢• {τ = τ} {τ' = τ'} ⊢e) = subst (_ ⊢ _ ∶_) (sym (ρτ[τ']≡ρτ[ρ↑τ'] ρ τ τ')) (⊢• (⊢ρ-preserves ⊢ρ ⊢e))
⊢ρ-preserves {ρ = ρ} {T = τ} ⊢ρ (⊢let ⊢e₂ ⊢e₁) = ⊢let (⊢ρ-preserves ⊢ρ ⊢e₂) (subst (_ ⊢ _ ∶_) (↑ρ·wkt≡wk·ρt τ ρ) (⊢ρ-preserves (⊢extᵣ ⊢ρ) ⊢e₁)) 
⊢ρ-preserves ⊢ρ ⊢τ = ⊢τ

⊢wk-preserves : ∀ {Γ : Ctx S} {t : Term S s} {T : Term S (type-of s)} {T' : Term S (type-of s')} →
  Γ ⊢ t ∶ T →
  Γ ▶ T' ⊢ wk t ∶ wk T 
⊢wk-preserves = ⊢ρ-preserves (⊢dropᵣ ⊢idᵣ)

σ[τ]≡[στ]·σ↑ : ∀ (τ : Type S₁) (σ : Sub S₁ S₂) →
  (singleₛ idₛ τ σσ→σ σ) ≡ ((extₛ σ τₛ) σσ→σ (singleₛ idₛ (sub σ τ)))
σ[τ]≡[στ]·σ↑ τ σ = fun-ext₂ 
  λ { _ (here refl) → refl
    ; _ (there x) → 
      begin 
        σ _ x
      ≡⟨ sym (idₛt≡t (σ _ x)) ⟩
        sub idₛ (σ _ x)
      ≡⟨ sym (ρt·σ≡ρ·σt (σ _ x) wkᵣ (singleₛ idₛ (sub σ τ))) ⟩
        sub (singleₛ idₛ (sub σ τ)) (wk (σ _ x))
      ∎
  }

σ·t[t']≡σ↑·t[σ·t'] : ∀ (σ : Sub S₁ S₂) (τ : Type (S₁ ▷ τₛ)) (τ' : Type S₁) →
  sub σ (τ [ τ' ]) ≡ (sub (extₛ σ _) τ) [ sub σ τ' ]  
σ·t[t']≡σ↑·t[σ·t'] σ τ τ' = 
   begin 
    sub σ (τ [ τ' ]) 
  ≡⟨ σt·σ≡σ·σt τ (singleₛ idₛ τ') σ ⟩
    sub (singleₛ idₛ τ' σσ→σ σ) τ
  ≡⟨ cong (λ σ → sub σ τ) (σ[τ]≡[στ]·σ↑ τ' σ) ⟩
   sub (extₛ σ τₛ σσ→σ singleₛ idₛ (sub σ τ')) τ
  ≡⟨ sym (σt·σ≡σ·σt τ (extₛ σ τₛ) (singleₛ idₛ (sub σ τ'))) ⟩
    (sub (extₛ σ _) τ) [ sub σ τ' ]  
  ∎

wk·σt≡↑σ·wkt : ∀ {s'} (σ : Sub S₁ S₂) (t : Term S₁ s) → 
  ren (wkᵣ {s = s'}) (sub σ t) ≡ sub (extₛ σ _) (ren wkᵣ t)
wk·σt≡↑σ·wkt σ t = begin 
    ren wkᵣ (sub σ t)
  ≡⟨ sym (σ↑·wkt≡wk·σt _ σ t) ⟩
    sub (extₛ σ _) (ren wkᵣ t)
  ∎

⊢σ↑ : ∀ {σ : Sub S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {T : Term S₁ (type-of s)} →
  σ ∶ Γ₁ ⇒ₛ Γ₂ →
  extₛ σ _ ∶ Γ₁ ▶ T ⇒ₛ (Γ₂ ▶ sub σ T)
⊢σ↑ {σ = σ} {T = τ} ⊢σ {eₛ} (here refl) = ⊢`x (sym (σ↑·wkt≡wk·σt _ σ τ))
⊢σ↑ {T = ⋆} ⊢σ {τₛ} (here refl) = ⊢τ
⊢σ↑ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T = T} ⊢σ (there x) = subst ((Γ₂ ▶ sub σ T) ⊢ wk (σ _ x) ∶_) (wk·σt≡↑σ·wkt σ (lookup Γ₁ x)) (⊢wk-preserves (⊢σ x))

-- [latex] block(preserves)
⊢σ-preserves : ∀ {σ : Sub S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} 
                 {t : Term S₁ s} {T : Term S₁ (type-of s)} →
  σ ∶ Γ₁ ⇒ₛ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (sub σ t) ∶ (sub σ T)
-- [latex] hide
⊢σ-preserves ⊢σ (⊢`x {x = x} refl) = ⊢σ x
⊢σ-preserves ⊢σ ⊢⊤ = ⊢⊤
⊢σ-preserves {σ = σ} ⊢σ (⊢λ {τ' = τ'} ⊢e) = ⊢λ 
  (subst (_ ⊢ _ ∶_) (σ↑·wkt≡wk·σt _ σ τ') (⊢σ-preserves (⊢σ↑ ⊢σ) ⊢e))
⊢σ-preserves ⊢σ (⊢Λ ⊢e) = ⊢Λ (⊢σ-preserves (⊢σ↑ ⊢σ) ⊢e)
⊢σ-preserves ⊢σ (⊢· ⊢e₁ ⊢e₂) = ⊢· (⊢σ-preserves ⊢σ ⊢e₁) (⊢σ-preserves ⊢σ ⊢e₂)
⊢σ-preserves {σ = σ} ⊢σ (⊢• {e = e} {τ = τ} {τ' = τ'} ⊢e) =
  subst (_ ⊢ sub σ (e • τ') ∶_) (sym (σ·t[t']≡σ↑·t[σ·t'] σ τ τ')) (⊢• (⊢σ-preserves ⊢σ ⊢e))
⊢σ-preserves {σ = σ} ⊢σ (⊢let {τ' = τ'} ⊢e₂ ⊢e₁) = ⊢let (⊢σ-preserves ⊢σ ⊢e₂) 
  (subst (_ ⊢ _ ∶_) (σ↑·wkt≡wk·σt _ σ τ') (⊢σ-preserves (⊢σ↑ ⊢σ) ⊢e₁))
⊢σ-preserves ⊢σ ⊢τ = ⊢τ

σ↑·wkt≡στ : ∀ (t : Term S₁ s) (t' : Term S₂ s') (σ : Sub S₁ S₂) →
  sub (singleₛ σ t') (wk t) ≡ sub σ t
σ↑·wkt≡στ t t' σ = ρt·σ≡ρ·σt t wkᵣ (singleₛ σ t')

⊢singleₛ : ∀ {σ : Sub S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : Term S₂ s} {T : Term S₁ (type-of s)} →
  σ ∶ Γ₁ ⇒ₛ Γ₂ →
  Γ₂ ⊢ t ∶ sub σ T →
  singleₛ σ t ∶ Γ₁ ▶ T ⇒ₛ Γ₂ 
⊢singleₛ {σ = σ} {t = t} {T = T} ⊢σ ⊢e (here refl) = subst (_ ⊢ t ∶_) (sym (σ↑·wkt≡στ T t σ)) ⊢e
⊢singleₛ {σ = σ} {Γ₁ = Γ₁} {t = t} ⊢σ ⊢e (there x) = subst (_ ⊢ σ _ x ∶_) (sym (σ↑·wkt≡στ (lookup Γ₁ x) t σ)) (⊢σ x)

τ[e]≡τ : ∀ {τ : Type S} {e : Expr S} → wk τ [ e ] ≡ τ  
τ[e]≡τ {τ = τ} {e = e} = 
  begin 
    wk τ [ e ]
  ≡⟨ σ↑·wkt≡στ τ e idₛ ⟩
    sub idₛ τ
  ≡⟨ idₛt≡t τ ⟩
    τ
  ∎

-- [latex] block(eepreserves)

e[e]-preserves :  ∀ {Γ : Ctx S} {e₁ : Expr (S ▷ eₛ)} {e₂ : Expr S} {τ τ' : Type S} →
  Γ ▶ τ ⊢ e₁ ∶ wk τ' →
  Γ ⊢ e₂ ∶ τ → 
  Γ ⊢ e₁ [ e₂ ] ∶ τ' 
-- [latex] hide
e[e]-preserves {τ = τ} ⊢e₁ ⊢e₂ = subst (_ ⊢ _ ∶_) τ[e]≡τ 
  (⊢σ-preserves (⊢singleₛ (⊢idₛ ⊢e₂) (subst (_ ⊢ _ ∶_) (sym (idₛt≡t τ)) ⊢e₂)) ⊢e₁) 

-- [latex] block(etpreserves) 

e[τ]-preserves :  ∀ {Γ : Ctx S} {e : Expr (S ▷ τₛ)} {τ : Type S} {τ' : Type (S ▷ τₛ)} →
  Γ ▶ ⋆ ⊢ e ∶ τ' →
  Γ ⊢ τ ∶ ⋆ →
  Γ ⊢ e [ τ ] ∶ τ' [ τ ] 
-- [latex] hide
e[τ]-preserves {τ = τ} ⊢e ⊢τ = ⊢σ-preserves (⊢singleₛ (⊢idₛ {t = τ} ⊢τ) ⊢τ) ⊢e

-- [latex] block(SubjectReduction)

subject-reduction : ∀ {Γ : Ctx S} →
  Γ ⊢ e ∶ τ →
  e ↪ e' →
  Γ ⊢ e' ∶ τ
subject-reduction (⊢· (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂) = e[e]-preserves ⊢e₁ ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e) = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e x) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)
subject-reduction (⊢• (⊢Λ ⊢e)) β-Λ = e[τ]-preserves ⊢e ⊢τ
subject-reduction (⊢• ⊢e) (ξ-• e↪e') = ⊢• (subject-reduction ⊢e e↪e')
subject-reduction (⊢let ⊢e₂ ⊢e₁) (β-let v₂) = e[e]-preserves ⊢e₁ ⊢e₂
subject-reduction (⊢let ⊢e₂ ⊢e₁) (ξ-let e₂↪e') = ⊢let 
  (subject-reduction ⊢e₂ e₂↪e') ⊢e₁  

-- [latex] end      