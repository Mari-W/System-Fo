open import Common using (_▷_; _▷▷_; Ctxable; ⊤ᶜ; ⊥ᶜ; r)
open import SystemF
open import SystemF-Overloading
open import Data.List using (List; [])
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; subst; sym; subst₂; module ≡-Reasoning)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open ≡-Reasoning

module DictionaryPassingTransform where

module SRC = SystemF-Overloading
module TGT = SystemF

-- Translation --------------------------------------------------------------------------

-- Sorts 

sort→ : SRC.Sort ⊤ᶜ → TGT.Sort ⊤ᶜ
sort→ eₛ = eₛ
sort→ oₛ = eₛ
sort→ τₛ = τₛ

sorts→ : SRC.Ctx SRC.S → TGT.Sorts
sorts→  ∅ = []
sorts→ (Γ ▸ c) = sorts→ Γ ▷ TGT.eₛ
sorts→ {S ▷ s} (Γ ▶ x) = sorts→ Γ ▷ sort→ s

-- Variables

member→ :  ∀ (Γ : SRC.Ctx SRC.S) → 
  SRC.Var SRC.S SRC.s → TGT.Var (sorts→ Γ) (sort→ SRC.s)
member→ (Γ ▶ τ) (here refl) = here refl
member→ (Γ ▶ τ) (there x) = there (member→ Γ x)
member→ (Γ ▸ c) x = there (member→ Γ x)

-- Types

type→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Type SRC.S →
  TGT.Type (sorts→ Γ)
type→ Γ (` x) = ` member→ Γ x
type→ Γ `⊤ = `⊤
type→ Γ (τ₁ ⇒ τ₂) = type→ Γ τ₁ ⇒ type→ Γ τ₂
type→ Γ (SRC.∀`α τ) = TGT.∀`α type→ (Γ ▶ tt) τ
type→ Γ (Ø o ∶ τ ⇒ τ') = type→ Γ τ ⇒ type→ Γ τ'

-- Wrappers 

stores→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Stores SRC.S SRC.s →
  TGT.Stores (sorts→ Γ) (sort→ SRC.s)
stores→ {s = eₛ} Γ τ = type→ Γ τ
stores→ {s = oₛ} Γ _ = `⊤
stores→ {s = τₛ} Γ _ = tt 

types→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Types SRC.S SRC.s →
  TGT.Stores (sorts→ Γ) (sort→ SRC.s)
types→ {s = eₛ} Γ τ = type→ Γ τ
types→ {s = oₛ} Γ τ = type→ Γ τ
types→ {s = τₛ} Γ _ = tt 

-- Context 

ctx→ : (Γ : SRC.Ctx SRC.S) → TGT.Ctx (sorts→ Γ)
ctx→ ∅ = ∅
ctx→ (Γ ▶ x) = (ctx→ Γ) ▶ stores→ Γ x
ctx→ (Γ ▸ (` o ∶ τ)) = (ctx→ Γ) ▶ type→ Γ τ

-- Renaming 
 
ren→ : ∀ {ρ : SRC.Ren SRC.S₁ SRC.S₂} (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) → 
  ρ SRC.∶ Γ₁ ⇒ᵣ Γ₂ →
  TGT.Ren (sorts→ Γ₁) (sorts→ Γ₂)
ren→ Γ Γ ⊢idᵣ = id
ren→ (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepᵣ ⊢ρ) = TGT.extᵣ (ren→ Γ₁ Γ₂ ⊢ρ)
ren→ Γ₁ (Γ₂ ▶ _) (⊢dropᵣ ⊢ρ) = TGT.dropᵣ (ren→ Γ₁ Γ₂ ⊢ρ)
ren→ (Γ₁ ▸ _) (Γ₂ ▸ _) (⊢keep-instᵣ ⊢ρ) = TGT.extᵣ (ren→ Γ₁ Γ₂ ⊢ρ) 
ren→ Γ₁ (Γ₂ ▸ _) (⊢drop-instᵣ ⊢ρ) = TGT.dropᵣ (ren→ Γ₁ Γ₂ ⊢ρ)

-- Substititution

sub→ : ∀ (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {σ : SRC.Sub SRC.S₁ SRC.S₂} → 
  σ SRC.∶ Γ₁ ⇒ₛ Γ₂ →
  TGT.Sub (sorts→ Γ₁) (sorts→ Γ₂)
sub→ Γ Γ ⊢idₛ = TGT.`_
sub→ (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepₛ ⊢σ) = TGT.extₛ (sub→ Γ₁ Γ₂ ⊢σ)
sub→ Γ₁ (Γ₂ ▶ _) (⊢dropₛ ⊢σ) = TGT.dropₛ (sub→ Γ₁ Γ₂ ⊢σ)
sub→ (Γ₁ ▶ tt) Γ₂ (⊢typeₛ {τ = τ} ⊢σ) = TGT.termₛ (sub→ Γ₁ Γ₂ ⊢σ) (type→ Γ₂ τ)
sub→ (Γ₁ ▸ _) (Γ₂ ▸ _) (⊢keep-instₛ ⊢σ) = TGT.extₛ (sub→ Γ₁ Γ₂ ⊢σ)
sub→ Γ₁ (Γ₂ ▸ _) (⊢drop-instₛ ⊢σ) = TGT.dropₛ (sub→ Γ₁ Γ₂ ⊢σ)

-- Type Preservation --------------------------------------------------------------------

-- Context

⊢ctx-inst : ∀ (Γ : SRC.Ctx SRC.S) {τ : SRC.Type SRC.S} {o} → 
  ctx→ (Γ ▸ (` o ∶ τ)) ≡ (ctx→ Γ) ▶ type→ Γ τ 
⊢ctx-inst (Γ ▶ x) = refl
⊢ctx-inst {S ▷ s} (Γ ▸ c) = refl

-- Renaming

⊢ren-member : (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ρ : SRC.Ren SRC.S₁ SRC.S₂} →
  (⊢ρ : ρ SRC.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (x : SRC.Var SRC.S₁ SRC.s) →
  (ren→ Γ₁ Γ₂ ⊢ρ) (member→ Γ₁ x) ≡ member→ Γ₂ (ρ x)   
⊢ren-member Γ Γ ⊢idᵣ x = refl
⊢ren-member (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepᵣ ⊢ρ) (here refl) = refl
⊢ren-member (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepᵣ ⊢ρ) (there x) = cong there (⊢ren-member Γ₁ Γ₂ ⊢ρ x)
⊢ren-member Γ₁ (Γ₂ ▶ _) (⊢dropᵣ ⊢ρ) x = cong there (⊢ren-member Γ₁ Γ₂ ⊢ρ x)
⊢ren-member (Γ₁ ▸ _) (Γ₂ ▸ _) (⊢keep-instᵣ ⊢ρ) x = cong there (⊢ren-member Γ₁ Γ₂ ⊢ρ x)
⊢ren-member Γ₁ (Γ₂ ▸ _) (⊢drop-instᵣ ⊢ρ) x = cong there (⊢ren-member Γ₁ Γ₂ ⊢ρ x)

⊢ren-type :  (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ρ : SRC.Ren SRC.S₁ SRC.S₂} →
  (⊢ρ : ρ SRC.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (τ : SRC.Type SRC.S₁) →
  TGT.ren (ren→ Γ₁ Γ₂ ⊢ρ) (type→ Γ₁ τ) ≡ type→ Γ₂ (SRC.ren ρ τ) 
⊢ren-type Γ₁ Γ₂ ⊢ρ (` x) = cong `_ (⊢ren-member Γ₁ Γ₂ ⊢ρ x)
⊢ren-type Γ₁ Γ₂ ⊢ρ `⊤ = refl
⊢ren-type Γ₁ Γ₂ ⊢ρ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⊢ren-type Γ₁ Γ₂ ⊢ρ τ₁) (⊢ren-type Γ₁ Γ₂ ⊢ρ τ₂)
⊢ren-type Γ₁ Γ₂ ⊢ρ (∀`α τ) = cong TGT.∀`α_ (⊢ren-type  (Γ₁ ▶ tt) (Γ₂ ▶ tt) (⊢keepᵣ ⊢ρ) τ)
⊢ren-type Γ₁ Γ₂ ⊢ρ (Ø (` o ∶ τ) ⇒ τ') = cong₂ _⇒_ (⊢ren-type Γ₁ Γ₂ ⊢ρ τ) (⊢ren-type Γ₁ Γ₂ ⊢ρ τ') 

⊢ext-id≡id : ∀ (x : SRC.Var (SRC.S ▷ SRC.s') SRC.s) → SRC.extᵣ SRC.idᵣ x ≡ SRC.idᵣ x
⊢ext-id≡id (here refl) = refl
⊢ext-id≡id (there x) = refl 

⊢ext-ρ₁≡ext-ρ₂ : ∀ {ρ₁ ρ₂ : SRC.Ren SRC.S₁ SRC.S₂} → 
 (∀ {s} (x : SRC.Var SRC.S₁ s) → ρ₁ x ≡ ρ₂ x) → 
 (∀ {s} (x : SRC.Var (SRC.S₁ ▷ SRC.s') s) → (SRC.extᵣ ρ₁) x ≡ (SRC.extᵣ ρ₂) x)
⊢ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂ (here refl) = refl
⊢ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂ (there x) = cong there (ρ₁≡ρ₂ x)

⊢ren-type-ext : ∀ {ρ₁ ρ₂ : SRC.Ren SRC.S₁ SRC.S₂} {τ : SRC.Type SRC.S₁} → 
  (∀ {s} (x : SRC.Var SRC.S₁ s) → ρ₁ x ≡ ρ₂ x) → 
  SRC.ren ρ₁ τ ≡ SRC.ren ρ₂ τ
⊢ren-type-ext {τ = ` x} ρ₁≡ρ₂ = cong `_ (ρ₁≡ρ₂ x)
⊢ren-type-ext {τ = `⊤} ρ₁≡ρ₂ = refl
⊢ren-type-ext {τ = τ₁ ⇒ τ₂} ρ₁≡ρ₂ = cong₂ _⇒_ (⊢ren-type-ext ρ₁≡ρ₂) (⊢ren-type-ext ρ₁≡ρ₂)
⊢ren-type-ext {τ = ∀`α τ} ρ₁≡ρ₂ = cong ∀`α_ (⊢ren-type-ext (⊢ext-ρ₁≡ext-ρ₂ ρ₁≡ρ₂))
⊢ren-type-ext {τ = Ø (` o ∶ τ) ⇒ τ'} ρ₁≡ρ₂ = cong₂ Ø_⇒_ (cong₂ _∶_ (cong `_ (ρ₁≡ρ₂ o)) (⊢ren-type-ext ρ₁≡ρ₂)) (⊢ren-type-ext ρ₁≡ρ₂) 

⊢ren-type-id : (τ : SRC.Type SRC.S) →
  SRC.ren SRC.idᵣ τ ≡ τ
⊢ren-type-id (` x) = refl
⊢ren-type-id `⊤ = refl
⊢ren-type-id (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⊢ren-type-id τ₁) (⊢ren-type-id τ₂)
⊢ren-type-id (∀`α τ) = cong ∀`α_ (trans (⊢ren-type-ext ⊢ext-id≡id) (⊢ren-type-id τ))
⊢ren-type-id (Ø ` o ∶ τ ⇒ τ') = cong₂ Ø_⇒_ (cong₂ _∶_ refl (⊢ren-type-id τ)) (⊢ren-type-id τ')

⊢wk : ∀ (Γ : SRC.Ctx SRC.S) {τ : SRC.Type SRC.S} {τ' : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  (ctx→ Γ ▶ type→ Γ τ) TGT.⊢ e ∶ type→ (Γ ▶ τ) (SRC.wk τ') →
  (ctx→ Γ ▶ type→ Γ τ) TGT.⊢ e ∶ TGT.wk (type→ Γ τ')
⊢wk Γ {τ = τ} {τ' = τ'} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ TGT.▶ type→ Γ τ) e) 
  (sym (⊢ren-type Γ (Γ ▶ τ) ⊢wkᵣ τ')) ⊢e  -- chain

⊢wk-inst : ∀ (Γ : SRC.Ctx SRC.S) {τ : SRC.Type SRC.S} {τ' : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} {o} →
  ctx→ (Γ ▸ (` o ∶ τ')) TGT.⊢ e ∶ type→ (Γ ▸ (` o ∶ τ')) τ →
  (ctx→ Γ ▶ type→ Γ τ') TGT.⊢ e ∶ TGT.wk (type→ Γ τ)
⊢wk-inst Γ {τ = τ} {τ' = τ'} {e = e} {o = o} ⊢e = subst₂ (λ Γ τ → Γ TGT.⊢ e ∶ τ) (⊢ctx-inst Γ {o = o})
  (subst (λ x → type→  (Γ ▸  (` o ∶ τ')) x ≡ TGT.ren there (type→ Γ τ)) (⊢ren-type-id τ) (sym (⊢ren-type Γ (Γ ▸  (` o ∶ τ')) ⊢wk-instᵣ τ))) ⊢e -- chain

⊢wk-decl : ∀ (Γ : SRC.Ctx SRC.S) {τ : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ eₛ)} →
  (ctx→ Γ ▶ `⊤) TGT.⊢ e ∶ type→ (SRC._▶_ {s = oₛ} Γ tt) (SRC.wk τ) →
  (ctx→ Γ ▶ `⊤) TGT.⊢ e ∶ TGT.wk (type→ Γ τ)
⊢wk-decl Γ {τ = τ} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ TGT.▶ TGT.`⊤) e) (sym (⊢ren-type Γ (Γ ▶ tt) ⊢wkᵣ τ)) ⊢e --chain

-- Substititution

⊢sub-member :  (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {σ : SRC.Sub SRC.S₁ SRC.S₂} →
  (⊢σ : σ SRC.∶ Γ₁ ⇒ₛ Γ₂) → 
  (x : SRC.Var SRC.S₁ τₛ) →
  TGT.sub (sub→ Γ₁ Γ₂ ⊢σ) (` member→ Γ₁ x) ≡ type→ Γ₂ (SRC.sub σ (` x))
⊢sub-member Γ Γ ⊢idₛ x = refl
⊢sub-member (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepₛ ⊢σ) (here refl) = refl
⊢sub-member (Γ₁ ▶ st) (Γ₂ ▶ _) (⊢keepₛ {σ = σ} ⊢σ) (there x) = trans 
  (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢σ x)) (⊢ren-type Γ₂ (Γ₂ ▶ SRC.sub' σ st) ⊢wkᵣ (σ x))
⊢sub-member Γ₁ (Γ₂ ▶ st) (⊢dropₛ {σ = σ} ⊢σ) x  = trans 
  (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢σ x)) (⊢ren-type Γ₂ (Γ₂ ▶ st) ⊢wkᵣ (σ x))
⊢sub-member (Γ₁ ▶ tt) Γ₂ (⊢typeₛ ⊢σ) (here refl) = refl
⊢sub-member (Γ₁ ▶ tt) Γ₂ (⊢typeₛ ⊢σ) (there x) = ⊢sub-member Γ₁ Γ₂ ⊢σ x 
⊢sub-member (Γ₁ ▸ (o ∶ τ)) (Γ₂ ▸ c) (⊢keep-instₛ {σ = σ} ⊢σ) x = trans (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢σ x)) 
  (subst (λ τ' → TGT.wk (type→ Γ₂ (SRC.sub σ (SRC.` x))) ≡ type→ (Γ₂ SRC.▸ (SRC.sub σ o SRC.∶ SRC.sub σ τ)) τ') 
  (⊢ren-type-id (σ x)) (⊢ren-type Γ₂ (Γ₂ ▸ (SRC.sub σ o ∶ SRC.sub σ τ)) ⊢wk-instᵣ (σ x))) --chain
⊢sub-member Γ₁ (Γ₂ ▸ (o ∶ τ)) (⊢drop-instₛ {σ = σ} ⊢σ) x = trans (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢σ x)) 
  (subst (λ τ' → TGT.wk (type→ Γ₂ (SRC.sub σ (SRC.` x))) ≡ type→ (Γ₂ SRC.▸ (o ∶ τ)) τ')  
  (⊢ren-type-id (σ x)) (⊢ren-type Γ₂ (Γ₂ ▸ (o ∶ τ)) ⊢wk-instᵣ (σ x))) --chain

⊢sub-type : ∀ {σ : SRC.Sub SRC.S₁ SRC.S₂} (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) → 
  (⊢σ : σ SRC.∶ Γ₁ ⇒ₛ Γ₂) → 
  (τ : SRC.Type SRC.S₁) →
  TGT.sub (sub→ Γ₁ Γ₂ ⊢σ) (type→ Γ₁ τ) ≡ type→ Γ₂ (SRC.sub σ τ) 
⊢sub-type Γ₁ Γ₂ ⊢σ (` x) = ⊢sub-member Γ₁ Γ₂ ⊢σ x
⊢sub-type Γ₁ Γ₂ ⊢σ `⊤ = refl
⊢sub-type Γ₁ Γ₂ ⊢σ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⊢sub-type Γ₁ Γ₂ ⊢σ τ₁) (⊢sub-type Γ₁ Γ₂ ⊢σ τ₂)
⊢sub-type Γ₁ Γ₂ ⊢σ (∀`α τ) = cong TGT.∀`α_ (⊢sub-type  (Γ₁ ▶ tt) (Γ₂ ▶ tt) (⊢keepₛ ⊢σ) τ)
⊢sub-type Γ₁ Γ₂ ⊢σ (Ø ` o ∶ τ ⇒ τ') = cong₂ _⇒_ (⊢sub-type Γ₁ Γ₂ ⊢σ τ) (⊢sub-type Γ₁ Γ₂ ⊢σ τ')

⊢single-type : (Γ : SRC.Ctx SRC.S₁) (τ : SRC.Type SRC.S₁) (τ' : SRC.Type (SRC.S₁ ▷ τₛ)) →  
  (type→ (Γ SRC.▶ tt) τ' TGT.[ type→ Γ τ ]) ≡ type→ Γ (τ' SRC.[ τ ])
⊢single-type Γ τ τ' = ⊢sub-type (Γ ▶ tt) Γ ⊢single-typeₛ τ'

⊢sub : ∀ (Γ : SRC.Ctx SRC.S) {τ : SRC.Type SRC.S} {τ' : SRC.Type (SRC.S ▷ τₛ)} {e : TGT.Expr (sorts→ Γ)} →
  ctx→ Γ TGT.⊢ e ∶ ∀`α type→ (Γ ▶ tt) τ' → 
  ctx→ Γ TGT.⊢ e • type→ Γ τ ∶ type→ Γ (τ' SRC.[ τ ])
⊢sub Γ {τ = τ} {τ' = τ'} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ) (e • type→ Γ τ)) (⊢single-type Γ τ τ') (⊢• ⊢e)

 
-- Type Preserving Translation ----------------------------------------------------------

-- Variables

⊢var→ : ∀ (Γ : SRC.Ctx SRC.S) {x : SRC.Var SRC.S eₛ} {τ : SRC.Type SRC.S} →
  SRC.wk-ctx Γ x ≡ τ →  
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ τ)
⊢var→ (Γ ▶ τ) {here refl} refl = here refl , ⊢ren-type Γ (Γ ▶ τ) ⊢wkᵣ τ
⊢var→ (_▶_ {s = s} Γ st) {there x'} {τ'} refl with ⊢var→ Γ {x = x'} refl 
... | x , Γx≡τ = there x , trans (cong TGT.wk Γx≡τ) (⊢ren-type Γ (Γ ▶ st) ⊢wkᵣ ((SRC.wk-stored x' (SRC.lookup Γ x'))))
⊢var→ (Γ ▸ c@(` o ∶ τ')) {x'} {τ} refl with ⊢var→ Γ {x = x'} refl 
... | x , Γx≡τ = there x , (
  begin                     
    TGT.wk (TGT.wk-stored x (TGT.lookup (ctx→ (Γ ▸ c)) (there x)))   
  ≡⟨ cong TGT.wk Γx≡τ ⟩ 
    TGT.wk (type→ Γ τ)
  ≡⟨ ⊢ren-type Γ (Γ ▸ (` o ∶ τ')) ⊢wk-instᵣ τ ⟩ 
    type→ (Γ ▸ c) (SRC.ren SRC.idᵣ τ)
  ≡⟨ cong (type→ (Γ ▸ c)) (⊢ren-type-id τ) ⟩ 
    type→ (Γ ▸ c) τ
  ∎)

⊢resolve→ : ∀ (Γ : SRC.Ctx SRC.S) →
  [ ` SRC.o ∶ SRC.τ ]∈ Γ → 
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ SRC.τ)
⊢resolve→ {S ▷ s} {o = o} {τ = τ} (Γ SRC.▸ c@(` o ∶ τ)) (here {Γ = Γ}) = here refl , (
  begin  
    TGT.wk-ctx (ctx→ Γ ▶ type→ Γ τ) (here refl)
  ≡⟨ ⊢ren-type Γ (Γ ▸ c) ⊢wk-instᵣ τ ⟩
    type→ (Γ ▸ (` o ∶ τ)) (SRC.ren SRC.idᵣ τ)
  ≡⟨ cong (type→ (Γ ▸ c)) (⊢ren-type-id τ) ⟩ 
    type→ (Γ ▸ c) τ
  ∎)
⊢resolve→ {S ▷ s} (Γ ▶ st) (under-bind {τ = τ} x) with ⊢resolve→ Γ x
... | x , Γx≡τ = there x , trans (cong TGT.wk Γx≡τ) (⊢ren-type Γ (Γ ▶ st) ⊢wkᵣ τ)
⊢resolve→ {S ▷ s} {τ = τ} (Γ ▸ c@(` o ∶ τ')) (under-inst {c' = _ ∶ τ'} x) with ⊢resolve→ Γ x 
... | x , Γx≡τ = there x , (
  begin                     
    TGT.wk (TGT.wk-stored x (TGT.lookup (ctx→ (Γ ▸ c)) (there x)))   
  ≡⟨ cong TGT.wk Γx≡τ ⟩ 
    TGT.wk (type→ Γ τ)
  ≡⟨ ⊢ren-type Γ (Γ ▸ (` o ∶ τ')) ⊢wk-instᵣ τ ⟩ 
    type→ (Γ ▸ c) (SRC.ren SRC.idᵣ τ)
  ≡⟨ cong (type→ (Γ ▸ c)) (⊢ren-type-id τ) ⟩ 
    type→ (Γ ▸ c) τ
  ∎)

-- Terms

⊢term→ : ∀ {Γ : SRC.Ctx SRC.S} {t : SRC.Term SRC.S SRC.s} {T : SRC.Types SRC.S SRC.s} →
  Γ SRC.⊢ t ∶ T →
  ∃[ t ] (ctx→ Γ) TGT.⊢ t ∶ (types→ Γ T)
⊢term→ {Γ = Γ} (⊢`x {x = x} Γx≡τ) with ⊢var→ Γ {x = x} Γx≡τ
... | x , Γx≡τ = (` x) , ⊢`x Γx≡τ
⊢term→ {Γ = Γ} (⊢`o ⊢o) with ⊢resolve→ Γ ⊢o 
... | x , Γx≡τ = (` x) , ⊢`x Γx≡τ
⊢term→ ⊢⊤ = tt , ⊢⊤
⊢term→ {Γ = Γ} (⊢λ ⊢e) with ⊢term→ ⊢e  
... | e , ⊢e = (λ`x→ e) , ⊢λ (⊢wk Γ ⊢e)
⊢term→ {Γ = Γ} (⊢Λ ⊢e) with ⊢term→ ⊢e
... | e , ⊢e = (Λ`α→ e) , ⊢Λ ⊢e
⊢term→ {Γ = Γ} (⊢ƛ {c = (` o ∶ τ)} ⊢e) with ⊢term→ ⊢e
... | e , ⊢e = (λ`x→ e) , ⊢λ (⊢wk-inst Γ ⊢e)
⊢term→ (⊢· ⊢e₁ ⊢e₂) with ⊢term→ ⊢e₁ | ⊢term→ ⊢e₂ 
... | e₁ , ⊢e₁ | e₂ , ⊢e₂ = e₁ · e₂ , ⊢· ⊢e₁ ⊢e₂
⊢term→ {Γ = Γ} (⊢• {τ = τ} ⊢e) with ⊢term→ ⊢e 
... | e , ⊢e = e • (type→ Γ τ) , ⊢sub Γ ⊢e
⊢term→  {Γ = Γ} (⊢⊘ ⊢e ⊢o) with ⊢term→ ⊢e | ⊢resolve→ Γ ⊢o
... | e , ⊢e | x , Γx≡τ = (e · ` x) , ⊢· ⊢e (⊢`x Γx≡τ)
⊢term→ {Γ = Γ} (⊢let ⊢e₂ ⊢e₁) with ⊢term→ ⊢e₂ | ⊢term→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁  = (`let`x= e₂ `in e₁) , ⊢let ⊢e₂ (⊢wk Γ ⊢e₁)
⊢term→ {Γ = Γ} (⊢decl ⊢e) with ⊢term→ ⊢e
... | e , ⊢e = (`let`x= tt `in e) , ⊢let ⊢⊤ (⊢wk-decl Γ ⊢e)
⊢term→ {Γ = Γ} (⊢inst {o = o} ⊢e₂ ⊢e₁) with ⊢term→ ⊢e₂ | ⊢term→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢let ⊢e₂ (⊢wk-inst Γ ⊢e₁)           