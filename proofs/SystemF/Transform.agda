open import Common using (_▷_; _▷▷_)
open import SystemF.Source
open import SystemF.Target
open import Function.Inverse using (_↔_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)

module SystemF.Transform where

module SRC = SystemF.Source
module TGT = SystemF.Target

sort→ : SRC.Sort → TGT.Sort
sort→ eₛ = eₛ
sort→ oₛ = eₛ
sort→ cₛ = eₛ
sort→ σₛ = σₛ

sorts→ : SRC.Ctx SRC.S → TGT.Sorts
sorts→ {[]} ∅ = []
sorts→ {S ▷ s} (Γ ▶ x) = (sorts→ Γ) ▷ sort→ s
sorts→ (Γ ▸ (o , σ)) = (sorts→ Γ) ▷ eₛ

member→ :  ∀ {Γ : SRC.Ctx SRC.S} → 
  SRC.s ∈ SRC.S → (sort→ SRC.s) ∈ (sorts→ Γ)
member→ {S ▷ s'} {s = s'} {Γ = Γ ▶ σ} (here refl) = here refl
member→ {S ▷ s'} {s = s} {Γ = Γ ▶ σ} (there x) = there (member→ x)
member→ {S ▷ s'} {s = s} {Γ = Γ ▸ (o , σ)} x = there (member→ {Γ = Γ} x)

mutual 
  cstr→ :  ∀ {Γ : SRC.Ctx SRC.S} →
    SRC.Cstr SRC.S →
    TGT.Type (sorts→ Γ)
  cstr→ (` _) = `⊤
  cstr→ ε = `⊤ 
  cstr→ (o ∶∶ σ) = type→ σ
  cstr→ (c₁ # c₂) = cstr→ c₁ ⇒ cstr→ c₂

  type→ : ∀ {Γ : SRC.Ctx SRC.S} →
    SRC.Type SRC.S →
    TGT.Type (sorts→ Γ)
  type→ (` x) = ` member→ x
  type→ `⊤ = `⊤
  type→ (σ ⇒ σ') = type→ σ ⇒ type→ σ'
  type→ {Γ = Γ} (SRC.∀`α ` _ ⇒ σ) = TGT.∀`α type→ {Γ = Γ ▶ tt} σ
  type→ {Γ = Γ} (SRC.∀`α ε ⇒ σ) = TGT.∀`α type→ {Γ = Γ ▶ tt} σ
  type→ {Γ = Γ} (SRC.∀`α c ⇒ σ) = TGT.∀`α cstr→ {Γ = Γ ▶ tt} c ⇒ type→ {Γ = Γ ▶ tt} σ

stores→ : ∀ {Γ : SRC.Ctx SRC.S} →
  SRC.Stores SRC.S SRC.s →
  TGT.Stores (sorts→ Γ) (sort→ SRC.s)
stores→ {s = eₛ} σ = type→ σ
stores→ {s = oₛ} _ = `⊤
stores→ {s = σₛ} _ = tt 

ctx→ : (Γ : SRC.Ctx SRC.S) → TGT.Ctx (sorts→ Γ)
ctx→ ∅ = ∅
ctx→ (_▶_ {s = eₛ} Γ σ) = (ctx→ Γ) ▶ type→ σ
ctx→ (_▶_ {s = oₛ} Γ _) = (ctx→ Γ) ▶ `⊤
ctx→ (_▶_ {s = σₛ} Γ _) = (ctx→ Γ) ▶ tt
ctx→ {S ▷ s} (Γ ▸ (o , σ)) = (ctx→ Γ) ▶ type→ σ

resolve→ : ∀ {Γ : SRC.Ctx SRC.S} →
  SRC.σ ∈ resolve Γ o → 
  ∃[ x ] (ctx→ Γ) TGT.⊢ ` x  ∶ (type→ SRC.σ)
resolve→ {S} {o} {σ} {Γ} a = {!  !}

⊢≡ : ∀ {Γ : SRC.Ctx SRC.S} → 
  SRC.wk-ctx Γ SRC.x ≡ SRC.σ → 
  TGT.wk-ctx (ctx→ Γ) (member→ SRC.x) ≡ (type→ SRC.σ)
⊢≡ refl = {!   !} 

⊢← : ∀ {Γ : SRC.Ctx SRC.S} {e : SRC.Expr (SRC.S ▷ σₛ)} {σ : SRC.Type (SRC.S ▷ σₛ)} →
  (c : SRC.Cstr (SRC.S ▷ σₛ)) →
  (Γ ▶ tt) ▸* c SRC.⊢ e ∶ σ →
  (→e : TGT.Expr (sorts→ ((Γ ▶ tt) ▸* c))) →
  (ctx→ ((Γ ▶ tt) ▸* c)) TGT.⊢ →e ∶ type→ σ →
  ∃[ e ] (ctx→ Γ) TGT.⊢ e ∶ type→ (SRC.∀`α c ⇒ σ)
⊢← = {!   !}

⊢→ : ∀ {Γ : SRC.Ctx SRC.S} →
  Γ SRC.⊢ SRC.e ∶ SRC.∀`α SRC.c ⇒ SRC.σ' →
  Γ SRC.⊢ SRC.c SRC.[ SRC.σ ] →
  (→e : TGT.Expr (sorts→ Γ)) →
  (ctx→ Γ) TGT.⊢ →e ∶ type→ (SRC.∀`α SRC.c ⇒ SRC.σ') →
  ∃[ e ] (ctx→ Γ) TGT.⊢ e ∶ type→ (SRC.σ' SRC.[ SRC.σ ])
⊢→ {c = ` x} ⊢e ⊢c e→ ⊢:→e = e→ · {!   !} , {!   !}
⊢→ {c = ε} {σ = σ} ⊢e ⊢–ε e→ ⊢:→e = e→ • type→ σ , {! ⊢-• ⊢:→e  !}
⊢→ {c = o ∶∶ σ'} {σ = σ} ⊢e ⊢c e→ ⊢:→e = {!   !}
⊢→ {c = c₁ # c₂} ⊢e (⊢–# ⊢c₁ ⊢c₂) e→ ⊢:→e = {!   !}
 
⊢∶→ : ∀ {Γ : SRC.Ctx SRC.S} →
  Γ SRC.⊢ SRC.t ∶ SRC.σ →
  ∃[ e ] (ctx→ Γ) TGT.⊢ e ∶ (type→ SRC.σ)
⊢∶→ (⊢-`x {x = x} r) = ` member→ x , ⊢-`x (⊢≡ r)
⊢∶→ {Γ = Γ} (⊢-`o x) with resolve→ {Γ = Γ} x 
... | x , ⊢x = ` x , ⊢x
⊢∶→ ⊢-⊤ = tt , ⊢-⊤
⊢∶→ {σ = σ} {Γ = Γ} (⊢-λ ⊢e) with ⊢∶→ ⊢e  
... | e , ⊢e = (λ`x→ e) , ⊢-λ {!  ⊢e !}
⊢∶→ (⊢-Λ {c = c} ⊢e) with ⊢∶→ ⊢e
... | e→ , ⊢:→e = ⊢← c ⊢e e→ ⊢:→e
⊢∶→ (⊢-· ⊢e₁ ⊢e₂) with ⊢∶→ ⊢e₁ | ⊢∶→ ⊢e₂ 
... | e₁ , ⊢e₁ | e₂ , ⊢e₂ = e₁ · e₂ , ⊢-· ⊢e₁ ⊢e₂
⊢∶→ (⊢-• ⊢e ⊢c) with ⊢∶→ ⊢e 
... | e→ , ⊢:→e = ⊢→ ⊢e ⊢c e→ ⊢:→e
⊢∶→ (⊢-let ⊢e₂ ⊢e₁) with ⊢∶→ ⊢e₂ | ⊢∶→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁  = (`let`x= e₂ `in e₁) , ⊢-let ⊢e₂ {!  ⊢e₁  !}
⊢∶→ (⊢-decl ⊢e) with ⊢∶→ ⊢e
... | e , ⊢e = (`let`x= tt `in e) , ⊢-let ⊢-⊤ {! ⊢e !}
⊢∶→ (⊢-inst ⊢e₂ ⊢e₁) with ⊢∶→ ⊢e₂ | ⊢∶→ ⊢e₁
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in {! e₁!}) , ⊢-let ⊢e₂ {! ⊢e₁  !}
    