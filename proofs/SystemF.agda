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
Ren S₁ S₂ = ∀ {s} → Var S₁ s → Var S₂ s

-- [latex] hide

idᵣ : Ren S S
idᵣ = id

wkᵣ : Ren S (S ▷ s) 
wkᵣ = there

-- [latex] block(renext)
extᵣ : Ren S₁ S₂ → Ren (S₁ ▷ s) (S₂ ▷ s)
extᵣ ρ (here refl) = here refl
extᵣ ρ (there x) = there (ρ x)
-- [latex] hide

dropᵣ : Ren S₁ S₂ → Ren S₁ (S₂ ▷ s) 
dropᵣ ρ x = there (ρ x)

-- [latex] block(ren)

ren : Ren S₁ S₂ → (Term S₁ s → Term S₂ s)
ren ρ (` x) = ` (ρ x)
ren ρ (λ`x→ e) = λ`x→ (ren (extᵣ ρ) e)
ren ρ (τ₁ ⇒ τ₂) = ren ρ τ₁ ⇒ ren ρ τ₂
-- ...
-- [latex] hide 
ren ρ tt = tt
ren ρ (Λ`α→ e) = Λ`α→ (ren (extᵣ ρ) e)
ren ρ (e₁ · e₂) = (ren ρ e₁) · (ren ρ e₂)
ren ρ (e • τ) = (ren ρ e) • (ren ρ τ)
ren ρ (let`x= e₂ `in e₁) = let`x= (ren ρ e₂) `in ren (extᵣ ρ) e₁
ren ρ `⊤ = `⊤
ren ρ (∀`α τ) = ∀`α (ren (extᵣ ρ) τ)
ren ρ ⋆ = ⋆

-- [latex] block(wk)

wk : Term S s → Term (S ▷ s') s
wk = ren there

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
    (extᵣ ρ) ∶ (Γ₁ ▶ T') ⇒ᵣ (Γ₂ ▶ ren ρ T')
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

⊢ρ-preserves-Γ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} (x : Var S₁ s) →
  ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
  ren ρ (lookup Γ₁ x) ≡ lookup Γ₂ (ρ x)
⊢ρ-preserves-Γ x ⊢ρ = {!       !}

⊢ρ-preserves : ∀ {ρ : Ren S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : Term S₁ s} {T : Term S₁ (type-of s)} →
  ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (ren ρ t) ∶ (ren ρ T)
⊢ρ-preserves ⊢ρ (⊢`x {x = x} refl) = ⊢`x (sym (⊢ρ-preserves-Γ x ⊢ρ))
⊢ρ-preserves ⊢ρ ⊢⊤ = ⊢⊤
⊢ρ-preserves ⊢ρ (⊢λ ⊢e) = {!   !} -- ⊢λ (subst (_ ⊢ _ ∶_) {!   !} (⊢• (⊢ρ-preserves (⊢extᵣ ⊢ρ) ⊢e)))
⊢ρ-preserves ⊢ρ (⊢Λ ⊢e) = ⊢Λ (⊢ρ-preserves (⊢extᵣ ⊢ρ) ⊢e)
⊢ρ-preserves ⊢ρ (⊢· ⊢e₁ ⊢e₂) = ⊢· (⊢ρ-preserves ⊢ρ ⊢e₁) (⊢ρ-preserves ⊢ρ ⊢e₂)
⊢ρ-preserves ⊢ρ (⊢• ⊢e) = {!   !} -- subst (_ ⊢ _ ∶_) {!   !} (⊢• (⊢ρ-preserves ⊢ρ ⊢e))
⊢ρ-preserves ⊢ρ (⊢let ⊢e₂ ⊢e₁) = ⊢let (⊢ρ-preserves ⊢ρ ⊢e₂) {!   !} 
⊢ρ-preserves ⊢ρ ⊢τ = ⊢τ

⊢wk-preserves : ∀ {Γ : Ctx S} {t : Term S s} {T : Term S (type-of s)} {T' : Term S (type-of s')} →
  Γ ⊢ t ∶ T →
  Γ ▶ T' ⊢ wk t ∶ wk T 
⊢wk-preserves = ⊢ρ-preserves (⊢dropᵣ ⊢idᵣ)

σ↑idₛ≡σ : ∀ (t : Term S₁ s) (t' : Term S₂ s') (σ : Sub S₁ S₂) →
  sub (singleₛ σ t') (wk t) ≡ sub σ t
σ↑idₛ≡σ t t' σ = {!   !}

_ρσ→σ_ : Ren S₁ S₂ → Sub S₂ S₃ → Sub S₁ S₃
(ρ ρσ→σ σ) _ x = σ _ (ρ x)

_σρ→σ_ : Sub S₁ S₂ → Ren S₂ S₃ → Sub S₁ S₃
(σ σρ→σ ρ) _ x = ren ρ (σ _ x)

↑σρ≡↑σ·↑ρ : ∀ s (ρ : Ren S₁ S₂) (σ : Sub S₂ S₃) →
  extₛ (ρ ρσ→σ σ) s ≡ (extᵣ ρ) ρσ→σ (extₛ σ s)
↑σρ≡↑σ·↑ρ s ρ σ = fun-ext₂ λ { _ (here refl) → refl
                             ; _ (there x) → refl }

mutual 
  ρ↑t·σ≡ρ·σ↑t : ∀ (t : Term (S₁ ▷ s') s) (ρ : Ren S₁ S₂) (σ : Sub S₂ S₃) →
    sub (extₛ σ _) (ren (extᵣ ρ) t) ≡ sub (extₛ (ρ ρσ→σ σ) _) t
  ρ↑t·σ≡ρ·σ↑t {s' = s'} t ρ σ = begin  
      sub (extₛ σ _) (ren (extᵣ ρ) t)
    ≡⟨ ρt·σ≡ρ·σt t (extᵣ ρ) (extₛ σ _) ⟩
      sub (extᵣ ρ ρσ→σ extₛ σ _) t
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

↑ρ·wkt≡wk·ρt : ∀ (t : Term S₁ s') (ρ : Ren S₁ S₂) →
  ren (extᵣ {s = s} ρ) (wk t) ≡ wk (ren ρ t) 
↑ρ·wkt≡wk·ρt = {!   !}

↑ρσ≡↑ρ·↑σ : ∀ s (σ : Sub S₁ S₂) (ρ : Ren S₂ S₃) →
  extₛ (σ σρ→σ ρ) s ≡ (extₛ σ _ σρ→σ extᵣ ρ)
↑ρσ≡↑ρ·↑σ s σ ρ =  fun-ext₂ λ { _ (here refl) → refl
                              ; _ (there x) →  sym (↑ρ·wkt≡wk·ρt (σ _ x) ρ) } 

mutual 
  σ↑t·ρ≡σ·ρ↑t : ∀ (t : Term (S₁ ▷ s') s) (σ : Sub S₁ S₂) (ρ : Ren S₂ S₃) →
    ren (extᵣ ρ) (sub (extₛ σ _) t) ≡ sub (extₛ (σ σρ→σ ρ) _) t
  σ↑t·ρ≡σ·ρ↑t {s' = s'} t σ ρ = begin 
      ren (extᵣ ρ) (sub (extₛ σ s') t)
    ≡⟨ σt·ρ≡σ·ρt t (extₛ σ _) (extᵣ ρ) ⟩
      sub (extₛ σ s' σρ→σ extᵣ ρ) t
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
  ≡⟨ ρt·σ≡ρ·σt t there (extₛ σ _) ⟩
    sub (σ σρ→σ there) t
  ≡⟨ sym (σt·ρ≡σ·ρt t σ there) ⟩
    ren there (sub σ t)
  ∎

σ·t[t']≡σ↑·t[σ·t'] : ∀ {s'} (σ : Sub S₁ S₂) (t : Term (S₁ ▷ s') s) (t' : Term S₁ s') →
  sub σ (t [ t' ]) ≡ (sub (extₛ σ _) t) [ sub σ t' ]  
σ·t[t']≡σ↑·t[σ·t'] = {!    !}

⊢σ↑ : ∀ {σ : Sub S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {T : Term S₁ (type-of s)} →
  σ ∶ Γ₁ ⇒ₛ Γ₂ →
  extₛ σ _ ∶ Γ₁ ▶ T ⇒ₛ (Γ₂ ▶ sub σ T)
⊢σ↑ {σ = σ} {T = τ} ⊢σ {eₛ} (here refl) = ⊢`x (sym (σ↑·wkt≡wk·σt _ σ τ))
⊢σ↑ {T = ⋆} ⊢σ {τₛ} (here refl) = ⊢τ
⊢σ↑ ⊢σ (there x) = {!    !}

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

⊢singleₛ : ∀ {σ : Sub S₁ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : Term S₂ s} {T : Term S₁ (type-of s)} →
  σ ∶ Γ₁ ⇒ₛ Γ₂ →
  Γ₂ ⊢ t ∶ sub σ T →
  singleₛ σ t ∶ Γ₁ ▶ T ⇒ₛ Γ₂ 
⊢singleₛ {σ = σ} {t = t} {T = T} ⊢σ ⊢e (here refl) = subst (_ ⊢ t ∶_) (sym (σ↑idₛ≡σ T t σ)) ⊢e
⊢singleₛ {σ = σ} {Γ₁ = Γ₁} {t = t} ⊢σ ⊢e (there x) = subst (_ ⊢ σ _ x ∶_) (sym (σ↑idₛ≡σ (lookup Γ₁ x) t σ)) (⊢σ x)

extₛidₛ≡idₛ : ∀ (x : Var (S ▷ s') s) → extₛ idₛ _ _ x ≡ idₛ _ x
extₛidₛ≡idₛ (here refl) = refl
extₛidₛ≡idₛ (there x) = refl 

⊢ext-σ₁≡ext-σ₂ : ∀ {σ₁ σ₂ : Sub S₁ S₂} → 
 (∀ {s} (x : Var S₁ s) → σ₁ _ x ≡ σ₂ _ x) → 
 (∀ {s} (x : Var (S₁ ▷ s') s) → (extₛ σ₁ _) _ x ≡ (extₛ σ₂ _) _ x)
⊢ext-σ₁≡ext-σ₂ σ₁≡σ₂ (here refl) = refl
⊢ext-σ₁≡ext-σ₂ σ₁≡σ₂ (there x) = cong wk (σ₁≡σ₂ x)

σ₁≡σ₂→σ₁τ≡σ₂τ : ∀ {σ₁ σ₂ : Sub S₁ S₂} (τ : Type S₁) → 
  (∀ {s} (x : Var S₁ s) → σ₁ _ x ≡ σ₂ _ x) → 
  sub σ₁ τ ≡ sub σ₂ τ
σ₁≡σ₂→σ₁τ≡σ₂τ (` x) σ₁≡σ₂ = σ₁≡σ₂ x
σ₁≡σ₂→σ₁τ≡σ₂τ `⊤ σ₁≡σ₂ = refl
σ₁≡σ₂→σ₁τ≡σ₂τ (τ₁ ⇒ τ₂) σ₁≡σ₂ = cong₂ _⇒_ (σ₁≡σ₂→σ₁τ≡σ₂τ τ₁ σ₁≡σ₂) (σ₁≡σ₂→σ₁τ≡σ₂τ τ₂ σ₁≡σ₂)
σ₁≡σ₂→σ₁τ≡σ₂τ (∀`α τ) σ₁≡σ₂ = cong ∀`α_ (σ₁≡σ₂→σ₁τ≡σ₂τ τ (⊢ext-σ₁≡ext-σ₂ σ₁≡σ₂))

idₛτ≡τ : (τ : Type S) →
  sub idₛ τ ≡ τ
idₛτ≡τ (` x) = refl
idₛτ≡τ `⊤ = refl
idₛτ≡τ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (idₛτ≡τ τ₁) (idₛτ≡τ τ₂)
idₛτ≡τ (∀`α τ) = cong ∀`α_ (trans (σ₁≡σ₂→σ₁τ≡σ₂τ τ extₛidₛ≡idₛ) (idₛτ≡τ τ))

⊢idₛ : ∀ {Γ : Ctx S} {t : Term S s} {T : Term S (type-of s)} (⊢t : Γ ⊢ t ∶ T) → idₛ ∶ Γ ⇒ₛ Γ
⊢idₛ {Γ = Γ} ⊢t {eₛ} x = ⊢`x (sym (idₛτ≡τ (lookup Γ x)))
⊢idₛ {Γ = Γ} ⊢t {τₛ} x with lookup Γ x
... | ⋆ = ⊢τ

τ[e]≡τ : ∀ {τ : Type S} {e : Expr S} → wk τ [ e ] ≡ τ  
τ[e]≡τ {τ = τ} {e = e} = 
  begin 
    wk τ [ e ]
  ≡⟨ σ↑idₛ≡σ τ e idₛ ⟩
    sub idₛ τ
  ≡⟨ idₛτ≡τ τ ⟩
    τ
  ∎

-- [latex] block(eepreserves)

e[e]-preserves :  ∀ {Γ : Ctx S} {e₁ : Expr (S ▷ eₛ)} {e₂ : Expr S} {τ τ' : Type S} →
  Γ ▶ τ ⊢ e₁ ∶ wk τ' →
  Γ ⊢ e₂ ∶ τ → 
  Γ ⊢ e₁ [ e₂ ] ∶ τ' 
-- [latex] hide
e[e]-preserves {τ = τ} ⊢e₁ ⊢e₂ = subst (_ ⊢ _ ∶_) τ[e]≡τ 
  (⊢σ-preserves (⊢singleₛ (⊢idₛ ⊢e₂) (subst (_ ⊢ _ ∶_) (sym (idₛτ≡τ τ)) ⊢e₂)) ⊢e₁) 

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