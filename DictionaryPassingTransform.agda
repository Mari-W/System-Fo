open import Common using (_▷_; _▷▷_; Ctxable; ⊤ᶜ; ⊥ᶜ; r)
open import SystemF
open import SystemF-Overloading
open import Function.Inverse using (_↔_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; subst; sym; subst₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (id; _∘_)

module DictionaryPassingTransform where

module SRC = SystemF-Overloading
module TGT = SystemF

-- Translation --------------------------------------------------------------------------

-- Sorts 

sort→ : SRC.Sort ⊤ᶜ → TGT.Sort ⊤ᶜ
sort→ eₛ = eₛ
sort→ oₛ = eₛ
sort→ σₛ = σₛ

sorts→ : SRC.Ctx SRC.S → TGT.Sorts
sorts→  ∅ = []
sorts→ (Γ ▸ c) = sorts→ Γ ▷ TGT.eₛ
sorts→ {S ▷ s} (Γ ▶ x) = sorts→ Γ ▷ sort→ s

-- Variables

member→ :  ∀ (Γ : SRC.Ctx SRC.S) → 
  SRC.Var SRC.S SRC.s → TGT.Var (sorts→ Γ) (sort→ SRC.s)
member→ (Γ ▶ σ) (here refl) = here refl
member→ (Γ ▶ σ) (there x) = there (member→ Γ x)
member→ (Γ ▸ c) x = there (member→ Γ x)

-- Types

type→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Type SRC.S →
  TGT.Type (sorts→ Γ)
type→ Γ (` x) = ` member→ Γ x
type→ Γ `⊤ = `⊤
type→ Γ (σ₁ ⇒ σ₂) = type→ Γ σ₁ ⇒ type→ Γ σ₂
type→ Γ (SRC.∀`α σ) = TGT.∀`α type→ (Γ ▶ tt) σ
type→ Γ (Ø o ∶ σ ⇒ σ') = type→ Γ σ ⇒ type→ Γ σ'

-- Wrappers 

stores→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Stores SRC.S SRC.s →
  TGT.Stores (sorts→ Γ) (sort→ SRC.s)
stores→ {s = eₛ} Γ σ = type→ Γ σ
stores→ {s = oₛ} Γ _ = `⊤
stores→ {s = σₛ} Γ _ = tt 

types→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Types SRC.S SRC.s →
  TGT.Types (sorts→ Γ) (sort→ SRC.s)
types→ {s = eₛ} Γ σ = type→ Γ σ
types→ {s = oₛ} Γ σ = type→ Γ σ
types→ {s = σₛ} Γ _ = tt 

-- Context 

ctx→ : (Γ : SRC.Ctx SRC.S) → TGT.Ctx (sorts→ Γ)
ctx→ ∅ = ∅
ctx→ (Γ ▶ x) = (ctx→ Γ) ▶ stores→ Γ x
ctx→ {S ▷ s} (Γ ▸ (` o ∶ σ)) = (ctx→ Γ) ▶ type→ Γ σ

-- Renaming 
 
ren→ : ∀ {ρ : SRC.Ren SRC.S₁ SRC.S₂} (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) → 
  ρ SRC.∶ Γ₁ ⇒ᵣ Γ₂ →
  TGT.Ren (sorts→ Γ₁) (sorts→ Γ₂)
ren→ Γ Γ ⊢idᵣ = id
ren→ (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepᵣ ⊢ρ) = TGT.extᵣ (ren→ Γ₁ Γ₂ ⊢ρ)
ren→ Γ₁ (Γ₂ ▶ _) (⊢dropᵣ ⊢ρ) = TGT.dropᵣ (ren→ Γ₁ Γ₂ ⊢ρ)
ren→ (Γ₁ ▸ _) (Γ₂ ▸ _) (⊢keep-instᵣ ⊢ρ) = TGT.extᵣ (ren→ Γ₁ Γ₂ ⊢ρ) 
ren→ Γ₁ (Γ₂ ▸ _) (⊢drop-instᵣ ⊢ρ) = λ x → there (ren→ Γ₁ Γ₂ ⊢ρ x)

-- Substititution

sub→ : ∀ (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ξ : SRC.Sub SRC.S₁ SRC.S₂} → 
  ξ SRC.∶ Γ₁ ⇒ₛ Γ₂ →
  TGT.Sub (sorts→ Γ₁) (sorts→ Γ₂)
sub→ Γ Γ ⊢idₛ = TGT.`_
sub→ (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepₛ ⊢ξ) = TGT.extₛ (sub→ Γ₁ Γ₂ ⊢ξ)
sub→ Γ₁ (Γ₂ ▶ _) (⊢dropₛ ⊢ξ) = TGT.dropₛ (sub→ Γ₁ Γ₂ ⊢ξ)
sub→ (Γ₁ ▶ tt) Γ₂ (⊢typeₛ {σ = σ} ⊢ξ) = TGT.termₛ (sub→ Γ₁ Γ₂ ⊢ξ) (type→ Γ₂ σ)
sub→ (Γ₁ ▸ _) (Γ₂ ▸ _) (⊢keep-instₛ ⊢ξ) = TGT.extₛ (sub→ Γ₁ Γ₂ ⊢ξ)
sub→ Γ₁ (Γ₂ ▸ _) (⊢drop-instₛ ⊢ξ) = TGT.dropₛ (sub→ Γ₁ Γ₂ ⊢ξ)

-- Type Preservation --------------------------------------------------------------------

-- Context

⊢ctx : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {o} → 
  ctx→ (Γ ▸ (` o ∶ σ)) ≡ (ctx→ Γ) ▶ type→ Γ σ 
⊢ctx (Γ ▶ x) = refl
⊢ctx {S ▷ s} (Γ ▸ c) = refl

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
  (σ : SRC.Type SRC.S₁) →
  TGT.ren (ren→ Γ₁ Γ₂ ⊢ρ) (type→ Γ₁ σ) ≡ type→ Γ₂ (SRC.ren ρ σ) 
⊢ren-type Γ₁ Γ₂ ⊢ρ (` x) = cong `_ (⊢ren-member Γ₁ Γ₂ ⊢ρ x)
⊢ren-type Γ₁ Γ₂ ⊢ρ `⊤ = refl
⊢ren-type Γ₁ Γ₂ ⊢ρ (σ₁ ⇒ σ₂) = cong₂ _⇒_ (⊢ren-type Γ₁ Γ₂ ⊢ρ σ₁) (⊢ren-type Γ₁ Γ₂ ⊢ρ σ₂)
⊢ren-type Γ₁ Γ₂ ⊢ρ (∀`α σ) = cong TGT.∀`α_ (⊢ren-type  (Γ₁ ▶ tt) (Γ₂ ▶ tt) (⊢keepᵣ ⊢ρ) σ)
⊢ren-type Γ₁ Γ₂ ⊢ρ (Ø (` o ∶ σ) ⇒ σ') = cong₂ _⇒_ (⊢ren-type Γ₁ Γ₂ ⊢ρ σ) (⊢ren-type Γ₁ Γ₂ ⊢ρ σ') 
 
⊢ren-type-id : (σ : SRC.Type SRC.S) →
  SRC.ren SRC.idᵣ σ ≡ σ
⊢ren-type-id (` x) = refl
⊢ren-type-id `⊤ = refl
⊢ren-type-id (σ₁ ⇒ σ₂) = cong₂ _⇒_ (⊢ren-type-id σ₁) (⊢ren-type-id σ₂)
⊢ren-type-id (∀`α σ) = cong ∀`α_ {!   !}
⊢ren-type-id (Ø ` o ∶ σ ⇒ σ') = cong₂ Ø_⇒_ (cong₂ _∶_ refl (⊢ren-type-id σ)) (⊢ren-type-id σ')

⊢wk : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {σ' : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  (ctx→ Γ ▶ type→ Γ σ) TGT.⊢ e ∶ type→ (Γ ▶ σ) (SRC.wk σ') →
  (ctx→ Γ ▶ type→ Γ σ) TGT.⊢ e ∶ TGT.wk (type→ Γ σ')
⊢wk Γ {σ = σ} {σ' = σ'} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ TGT.▶ type→ Γ σ) e) 
  (sym (⊢ren-type Γ (Γ ▶ σ) ⊢wkᵣ σ')) ⊢e 

⊢wk-inst : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {σ' : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  ctx→ (Γ ▸ (` o ∶ σ')) TGT.⊢ e ∶ type→ (Γ ▸ (` o ∶ σ')) σ →
  (ctx→ Γ ▶ type→ Γ σ') TGT.⊢ e ∶ TGT.wk (type→ Γ σ)
⊢wk-inst {o = o} Γ {σ = σ} {σ' = σ'} {e = e} ⊢e = subst₂ (λ Γ σ → Γ TGT.⊢ e ∶ σ) (⊢ctx Γ) 
  (subst (λ x → type→  (Γ ▸  (` o ∶ σ')) x ≡ TGT.ren there (type→ Γ σ)) (⊢ren-type-id σ) (sym (⊢ren-type Γ (Γ ▸  (` o ∶ σ')) ⊢wk-instᵣ σ))) ⊢e

⊢wk-decl : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ eₛ)} →
  (ctx→ Γ ▶ `⊤) TGT.⊢ e ∶ type→ (SRC._▶_ {s = oₛ} Γ tt) (SRC.wk σ) →
  (ctx→ Γ ▶ `⊤) TGT.⊢ e ∶ TGT.wk (type→ Γ σ)
⊢wk-decl Γ {σ = σ} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ TGT.▶ TGT.`⊤) e) (sym (⊢ren-type Γ (Γ ▶ tt) ⊢wkᵣ σ)) ⊢e

-- Substititution

⊢sub-member :  (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ξ : SRC.Sub SRC.S₁ SRC.S₂} →
  (⊢ξ : ξ SRC.∶ Γ₁ ⇒ₛ Γ₂) → 
  (x : SRC.Var SRC.S₁ σₛ) →
  TGT.sub (sub→ Γ₁ Γ₂ ⊢ξ) (` member→ Γ₁ x) ≡ type→ Γ₂ (SRC.sub ξ (` x))
⊢sub-member Γ Γ ⊢idₛ x = refl
⊢sub-member (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepₛ ⊢ξ) (here refl) = refl
⊢sub-member (Γ₁ ▶ st) (Γ₂ ▶ _) (⊢keepₛ {ξ = ξ} ⊢ξ) (there x) = trans 
  (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢ξ x)) (⊢ren-type Γ₂ (Γ₂ ▶ SRC.sub' ξ st) ⊢wkᵣ (ξ x))
⊢sub-member Γ₁ (Γ₂ ▶ st) (⊢dropₛ {ξ = ξ} ⊢ξ) x  = trans 
  (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢ξ x)) (⊢ren-type Γ₂ (Γ₂ ▶ st) ⊢wkᵣ (ξ x))
⊢sub-member (Γ₁ ▶ tt) Γ₂ (⊢typeₛ ⊢ξ) (here refl) = refl
⊢sub-member (Γ₁ ▶ tt) Γ₂ (⊢typeₛ ⊢ξ) (there x) = ⊢sub-member Γ₁ Γ₂ ⊢ξ x 
⊢sub-member (Γ₁ ▸ (o ∶ σ)) (Γ₂ ▸ c) (⊢keep-instₛ {ξ = ξ} ⊢ξ) x = trans (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢ξ x)) 
  (subst (λ σ' → TGT.wk (type→ Γ₂ (SRC.sub ξ (SRC.` x))) ≡ type→ (Γ₂ SRC.▸ (SRC.sub ξ o SRC.∶ SRC.sub ξ σ)) σ') 
  (⊢ren-type-id (ξ x)) (⊢ren-type Γ₂ (Γ₂ ▸ (SRC.sub ξ o ∶ SRC.sub ξ σ)) ⊢wk-instᵣ (ξ x)))
⊢sub-member Γ₁ (Γ₂ ▸ (o ∶ σ)) (⊢drop-instₛ {ξ = ξ} ⊢ξ) x = trans (cong TGT.wk (⊢sub-member Γ₁ Γ₂ ⊢ξ x)) 
  (subst (λ σ' → TGT.wk (type→ Γ₂ (SRC.sub ξ (SRC.` x))) ≡ type→ (Γ₂ SRC.▸ (o ∶ σ)) σ') 
  (⊢ren-type-id (ξ x)) (⊢ren-type Γ₂ (Γ₂ ▸ (o ∶ σ)) ⊢wk-instᵣ (ξ x)))

⊢sub-type : ∀ {ξ : SRC.Sub SRC.S₁ SRC.S₂} (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) → 
  (⊢ξ : ξ SRC.∶ Γ₁ ⇒ₛ Γ₂) → 
  (σ : SRC.Type SRC.S₁) →
  TGT.sub (sub→ Γ₁ Γ₂ ⊢ξ) (type→ Γ₁ σ) ≡ type→ Γ₂ (SRC.sub ξ σ) 
⊢sub-type Γ₁ Γ₂ ⊢ξ (` x) = ⊢sub-member Γ₁ Γ₂ ⊢ξ x
⊢sub-type Γ₁ Γ₂ ⊢ξ `⊤ = refl
⊢sub-type Γ₁ Γ₂ ⊢ξ (σ₁ ⇒ σ₂) = cong₂ _⇒_ (⊢sub-type Γ₁ Γ₂ ⊢ξ σ₁) (⊢sub-type Γ₁ Γ₂ ⊢ξ σ₂)
⊢sub-type Γ₁ Γ₂ ⊢ξ (∀`α σ) = cong TGT.∀`α_ (⊢sub-type  (Γ₁ ▶ tt) (Γ₂ ▶ tt) (⊢keepₛ ⊢ξ) σ)
⊢sub-type Γ₁ Γ₂ ⊢ξ (Ø ` o ∶ σ ⇒ σ') = cong₂ _⇒_ (⊢sub-type Γ₁ Γ₂ ⊢ξ σ) (⊢sub-type Γ₁ Γ₂ ⊢ξ σ')

⊢intro-type : (Γ : SRC.Ctx SRC.S₁) (σ : SRC.Type SRC.S₁) (σ' : SRC.Type (SRC.S₁ ▷ σₛ)) →  
  (type→ (Γ SRC.▶ tt) σ' TGT.[ type→ Γ σ ]) ≡ type→ Γ (σ' SRC.[ σ ])
⊢intro-type Γ σ σ' = ⊢sub-type (Γ ▶ tt) Γ ⊢intro-typeₛ σ'

⊢sub : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {σ' : SRC.Type (SRC.S ▷ σₛ)} {e : TGT.Expr (sorts→ Γ)} →
  ctx→ Γ TGT.⊢ e ∶ ∀`α type→ (Γ ▶ tt) σ' → 
  ctx→ Γ TGT.⊢ e • type→ Γ σ ∶ type→ Γ (σ' SRC.[ σ ])
⊢sub Γ {σ = σ} {σ' = σ'} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ) (e • type→ Γ σ)) (⊢intro-type Γ σ σ') (⊢• ⊢e)

 
-- Type Preserving Translation ----------------------------------------------------------

-- Variables

⊢var→ : ∀ (Γ : SRC.Ctx SRC.S) {x : SRC.Var SRC.S eₛ} {σ : SRC.Type SRC.S} →
  SRC.wk-ctx Γ x ≡ σ →  
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ σ)
⊢var→ Γ {x} {σ} refl = member→ Γ x , {!   !}

⊢resolve→ : ∀ (Γ : SRC.Ctx SRC.S) →
  [ ` SRC.o ∶ SRC.σ ]∈ Γ → 
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ SRC.σ)
⊢resolve→ {S ▷ s} {o} {σ} Γ'@(Γ SRC.▸ (` o ∶ σ)) (here {Γ = Γ}) = here refl , {!   !}
⊢resolve→ {S ▷ eₛ} (Γ ▶ σ') (under-bind {σ = σ} t) with ⊢resolve→ Γ t
... | t , eq = there t , trans (cong TGT.wk eq) (⊢ren-type Γ (Γ ▶ σ') ⊢wkᵣ σ)
⊢resolve→ {S ▷ oₛ} (Γ ▶ _) (under-bind {σ = σ} t) with ⊢resolve→ Γ t
... | t , eq = there t , trans (cong TGT.wk eq) (⊢ren-type Γ (Γ ▶ tt) ⊢wkᵣ σ)
⊢resolve→ {S ▷ σₛ} (Γ ▶ σ') (under-bind {σ = σ} t) with ⊢resolve→ Γ t
... | t , eq = there t , trans (cong TGT.wk eq) (⊢ren-type Γ (Γ ▶ σ') ⊢wkᵣ σ)
⊢resolve→ {S ▷ s} {σ = σ} (Γ ▸ (_ ∶ σ')) (under-inst {_} {_} {_} {_ ∶ σ'} t) with ⊢resolve→ Γ t 
... | t , eq = there t , {!   !}

-- Terms

⊢term→ : ∀ {Γ : SRC.Ctx SRC.S} {t : SRC.Term SRC.S SRC.s} {T : SRC.Types SRC.S SRC.s} →
  Γ SRC.⊢ t ∶ T →
  ∃[ t ] (ctx→ Γ) TGT.⊢ t ∶ (types→ Γ T)
⊢term→ {Γ = Γ} (⊢`x {x = x} eq) with ⊢var→ Γ {x = x} eq
... | x , Γx≡σ = (` x) , ⊢`x Γx≡σ
⊢term→ {Γ = Γ} (⊢`o ⊢o) with ⊢resolve→ Γ ⊢o 
... | x , Γx≡σ = (` x) , ⊢`x Γx≡σ
⊢term→ ⊢⊤ = tt , ⊢⊤
⊢term→ {Γ = Γ} (⊢λ ⊢e) with ⊢term→ ⊢e  
... | e , ⊢e = (λ`x→ e) , ⊢λ (⊢wk Γ ⊢e)
⊢term→ {Γ = Γ} (⊢Λ ⊢e) with ⊢term→ ⊢e
... | e , ⊢e = (Λ`α→ e) , ⊢Λ ⊢e
⊢term→ {Γ = Γ} (⊢ƛ {c = (` o ∶ σ)} ⊢e) with ⊢term→ ⊢e
... | e , ⊢e = (λ`x→ e) , ⊢λ (⊢wk-inst Γ ⊢e)
⊢term→ (⊢· ⊢e₁ ⊢e₂) with ⊢term→ ⊢e₁ | ⊢term→ ⊢e₂ 
... | e₁ , ⊢e₁ | e₂ , ⊢e₂ = e₁ · e₂ , ⊢· ⊢e₁ ⊢e₂
⊢term→ {Γ = Γ} (⊢• {σ = σ} ⊢e) with ⊢term→ ⊢e 
... | e , ⊢e = e • (type→ Γ σ) , ⊢sub Γ ⊢e
⊢term→  {Γ = Γ} (⊢⊘ ⊢e ⊢o) with ⊢term→ ⊢e | ⊢resolve→ Γ ⊢o
... | e , ⊢e | x , Γx≡σ = (e · ` x) , ⊢· ⊢e (⊢`x Γx≡σ)
⊢term→ {Γ = Γ} (⊢let ⊢e₂ ⊢e₁) with ⊢term→ ⊢e₂ | ⊢term→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁  = (`let`x= e₂ `in e₁) , ⊢let ⊢e₂ (⊢wk Γ ⊢e₁)
⊢term→ {Γ = Γ} (⊢decl ⊢e) with ⊢term→ ⊢e
... | e , ⊢e = (`let`x= tt `in e) , ⊢let ⊢⊤ (⊢wk-decl Γ ⊢e)
⊢term→ {Γ = Γ} (⊢inst {o = o} ⊢e₂ ⊢e₁) with ⊢term→ ⊢e₂ | ⊢term→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢let ⊢e₂ (⊢wk-inst Γ ⊢e₁)   