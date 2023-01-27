open import Common using (_▷_; _▷▷_; Ctxable; ⊤ᶜ; ⊥ᶜ; r; cong₃)
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
ren→ (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepᵣ ⊢ren) = TGT.extᵣ (ren→ Γ₁ Γ₂ ⊢ren)
ren→ Γ₁ (Γ₂ ▶ _) (⊢dropᵣ ⊢ren) = TGT.dropᵣ (ren→ Γ₁ Γ₂ ⊢ren)
ren→ (Γ₁ ▸ _) (Γ₂ ▸ _) (⊢keep-instᵣ ⊢ren) = TGT.extᵣ (ren→ Γ₁ Γ₂ ⊢ren) 
ren→ Γ₁ (Γ₂ ▸ _) (⊢drop-instᵣ ⊢ren) = λ x → there (ren→ Γ₁ Γ₂ ⊢ren x)

-- Type Preservation --------------------------------------------------------------------

-- Context

⊢ctx : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {o} → 
  (ctx→ Γ) ▶ type→ Γ σ ≡ ctx→ (Γ ▸ (` o ∶ σ)) 
⊢ctx (Γ ▶ x) = refl
⊢ctx {S ▷ s} (Γ ▸ c) = refl

-- Renaming

⊢ren-member : (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ρ : SRC.Ren SRC.S₁ SRC.S₂} →
  (ope : ρ SRC.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (x : SRC.Var SRC.S₁ SRC.s) →
  (ren→ Γ₁ Γ₂ ope) (member→ Γ₁ x) ≡ member→ Γ₂ (ρ x)   
⊢ren-member Γ Γ ⊢idᵣ x = refl
⊢ren-member (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepᵣ ⊢ren) (here refl) = refl
⊢ren-member (Γ₁ ▶ _) (Γ₂ ▶ _) (⊢keepᵣ ⊢ren) (there x) = cong there (⊢ren-member Γ₁ Γ₂ ⊢ren x)
⊢ren-member Γ₁ (Γ₂ ▶ _) (⊢dropᵣ ⊢ren) x = cong there (⊢ren-member Γ₁ Γ₂ ⊢ren x)
⊢ren-member (Γ₁ ▸ _) (Γ₂ ▸ _) {- ρ-} (⊢keep-instᵣ ⊢ren) (here refl) = cong there (⊢ren-member Γ₁ Γ₂ ⊢ren (here refl))
⊢ren-member (Γ₁ ▸ _) (Γ₂ ▸ _) (⊢keep-instᵣ ⊢ren) (there x) = cong there (⊢ren-member Γ₁ Γ₂ ⊢ren (there x))
⊢ren-member Γ₁ (Γ₂ ▸ _) (⊢drop-instᵣ ⊢ren) x = cong there (⊢ren-member Γ₁ Γ₂ ⊢ren x)

⊢ren-type : (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ρ : SRC.Ren SRC.S₁ SRC.S₂} →
  (ope : ρ SRC.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (σ : SRC.Type SRC.S₁) →
  TGT.ren (ren→ Γ₁ Γ₂ ope) (type→ Γ₁ σ) ≡ type→ Γ₂ (SRC.ren ρ σ) 
⊢ren-type Γ₁ Γ₂ ⊢ren (` x) = cong `_ (⊢ren-member Γ₁ Γ₂ ⊢ren x)
⊢ren-type Γ₁ Γ₂ ⊢ren `⊤ = refl
⊢ren-type Γ₁ Γ₂ ⊢ren (σ₁ ⇒ σ₂) = cong₂ _⇒_ (⊢ren-type Γ₁ Γ₂ ⊢ren σ₁) (⊢ren-type Γ₁ Γ₂ ⊢ren σ₂)
⊢ren-type Γ₁ Γ₂ ⊢ren (SRC.∀`α σ) = cong TGT.∀`α_ (⊢ren-type  (Γ₁ ▶ tt) (Γ₂ ▶ tt) (⊢keepᵣ ⊢ren) σ)
⊢ren-type Γ₁ Γ₂ ⊢ren (Ø (` o ∶ σ) ⇒ σ') = cong₂ _⇒_ (⊢ren-type Γ₁ Γ₂ ⊢ren σ) (⊢ren-type Γ₁ Γ₂ ⊢ren σ') 

⊢wk : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {σ' : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  (ctx→ Γ ▶ type→ Γ σ) TGT.⊢ e ∶ type→ (Γ ▶ σ) (SRC.wk σ') →
  (ctx→ Γ ▶ type→ Γ σ) TGT.⊢ e ∶ TGT.wk (type→ Γ σ')
⊢wk Γ {σ = σ} {σ' = σ'} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ TGT.▶ type→ Γ σ) e) 
  (sym (⊢ren-type Γ (Γ ▶ σ) ⊢wkᵣ σ')) ⊢e 

⊢wk-inst : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {σ' : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  ctx→ (Γ ▸ (` o ∶ σ')) TGT.⊢ e ∶ type→ (Γ ▸ (` o ∶ σ')) σ →
  (ctx→ Γ ▶ type→ Γ σ') TGT.⊢ e ∶ TGT.wk (type→ Γ σ)
⊢wk-inst Γ {σ = σ} {σ' = σ'} {e = e} ⊢e = subst₂ (λ Γ σ → Γ TGT.⊢ e ∶ σ) (sym (⊢ctx Γ)) {! sym (⊢ren-type ? ? ? ?) !} ⊢e

⊢wk-decl : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ eₛ)} →
  (ctx→ Γ ▶ `⊤) TGT.⊢ e ∶ type→ (SRC._▶_ {s = oₛ} Γ tt) (SRC.wk σ) →
  (ctx→ Γ ▶ `⊤) TGT.⊢ e ∶ TGT.wk (type→ Γ σ)
⊢wk-decl Γ {σ = σ} {e = e} ⊢e = subst (TGT._⊢_∶_ (ctx→ Γ TGT.▶ TGT.`⊤) e) (sym (⊢ren-type Γ (Γ ▶ tt) ⊢wkᵣ σ)) ⊢e

-- Substititution

⊢sub-type : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {σ' : SRC.Type (SRC.S ▷ σₛ)} {e : TGT.Expr (sorts→ Γ)} →
  ctx→ Γ TGT.⊢ e ∶ TGT.∀`α type→ (Γ SRC.▶ tt) σ' → 
  ctx→ Γ TGT.⊢ e TGT.• type→ Γ σ ∶ type→ Γ (σ' SRC.[ σ ])
⊢sub-type = {!   !}
 
-- Type Preserving Translation ----------------------------------------------------------

-- Variables

⊢var→ : ∀ (Γ : SRC.Ctx SRC.S) {x : SRC.Var SRC.S eₛ} {σ : SRC.Type SRC.S} →
  SRC.wk-ctx Γ x ≡ σ →  
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ σ)
⊢var→ Γ {x} {σ} refl = member→ Γ x , {!   !}

⊢resolve→ : ∀ (Γ : SRC.Ctx SRC.S) →
  [ ` SRC.o ∶ SRC.σ ]∈ Γ → 
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ SRC.σ)
⊢resolve→ {S ▷ s} {o} {σ} Γ'@(Γ SRC.▸ (` o ∶ σ)) (here {Γ = Γ}) = {!   !} {- with ⊢id-type→ σ
... | eq = here refl ,  {! cong  ? (⊢ren-type Γ Γ' (wk-ope-inst Γ) σ) !} -}
⊢resolve→ {S ▷ s} (Γ ▶ σ) (under-bind x) with ⊢resolve→ Γ x
⊢resolve→ {S ▷ eₛ} (Γ ▶ σ') (under-bind {σ = σ} x) | t , eq = 
  there t , trans (cong TGT.wk eq) (⊢ren-type Γ (Γ ▶ σ') ⊢wkᵣ σ)
⊢resolve→ {S ▷ oₛ} (Γ ▶ _) (under-bind {σ = σ} x) | t , eq = 
  there t , trans (cong TGT.wk eq) (⊢ren-type Γ (Γ ▶ tt) ⊢wkᵣ σ)
⊢resolve→ {S ▷ σₛ} (Γ ▶ σ') (under-bind {σ = σ} x) | t , eq = 
  there t , trans (cong TGT.wk eq) (⊢ren-type Γ (Γ ▶ σ') ⊢wkᵣ σ)
⊢resolve→ {S ▷ s} Γ'@(Γ ▸ (_ ∶ σ')) (under-inst {c' = `o ∶ σ} t) with ⊢resolve→ Γ t
... | t , eq = there t , {!   !}

-- Terms

⊢term→ : ∀ {Γ : SRC.Ctx SRC.S} {t : SRC.Term SRC.S SRC.s} {T : SRC.Types SRC.S SRC.s} →
  Γ SRC.⊢ t ∶ T →
  ∃[ t ] (ctx→ Γ) TGT.⊢ t ∶ (types→ Γ T)
⊢term→ {Γ = Γ} (⊢`x {x = x} eq) with ⊢var→ Γ {x = x} eq
... | x , Γx≡σ = (` x) , ⊢`x Γx≡σ
⊢term→ {Γ = Γ} (⊢`o o) with ⊢resolve→ Γ o 
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
... | e , ⊢e = e • (type→ Γ σ) , ⊢sub-type Γ ⊢e
⊢term→  {Γ = Γ} (⊢⊘ ⊢e c) with ⊢term→ ⊢e | ⊢resolve→ Γ c 
... | e , ⊢e | x , Γx≡σ = (e · ` x) , ⊢· ⊢e (⊢`x Γx≡σ)
⊢term→ {Γ = Γ} (⊢let ⊢e₂ ⊢e₁) with ⊢term→ ⊢e₂ | ⊢term→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁  = (`let`x= e₂ `in e₁) , ⊢let ⊢e₂ (⊢wk Γ ⊢e₁)
⊢term→ {Γ = Γ} (⊢decl ⊢e) with ⊢term→ ⊢e
... | e , ⊢e = (`let`x= tt `in e) , ⊢let ⊢⊤ (⊢wk-decl Γ ⊢e)
⊢term→ {Γ = Γ} (⊢inst {o = o} ⊢e₂ ⊢e₁) with ⊢term→ ⊢e₂ | ⊢term→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢let ⊢e₂ (⊢wk-inst Γ ⊢e₁)