open import Common using (_▷_; _▷▷_; Ctxable; ⊤ᶜ; ⊥ᶜ; r)
open import SystemF.Source
open import SystemF.Target
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

module SystemF.Transform where

module SRC = SystemF.Source
module TGT = SystemF.Target

sort→ : SRC.Sort ⊤ᶜ → TGT.Sort ⊤ᶜ
sort→ eₛ = eₛ
sort→ oₛ = eₛ
sort→ σₛ = σₛ

sorts→ : SRC.Ctx SRC.S → TGT.Sorts
sorts→  ∅ = []
sorts→ {S ▷ s} (Γ ▶ x) = sorts→ Γ ▷ sort→ s
sorts→ (Γ ▸ (o , σ)) = sorts→ Γ ▷ TGT.eₛ

member→ :  ∀ (Γ : SRC.Ctx SRC.S) → 
  SRC.s ∈ SRC.S → (sort→ SRC.s) ∈ (sorts→ Γ)
member→ {S ▷ s'} {s = s'} (Γ ▶ σ) (here refl) = here refl
member→ {S ▷ s'} {s = s} (Γ ▶ σ) (there x) = there (member→ Γ x)
member→ {S ▷ s'} {s = s} (Γ ▸ (o , σ)) x = there (member→ Γ x)

type→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Type SRC.S →
  TGT.Type (sorts→ Γ)
type→ Γ (` x) = ` member→ Γ x
type→ Γ `⊤ = `⊤
type→ Γ (σ ⇒ σ') = type→ Γ σ ⇒ type→ Γ σ'
type→ Γ (SRC.∀`α c ⇒ σ) = TGT.∀`α cstr→ (Γ ▶ tt) c (type→ (Γ ▶ tt) σ)
  where cstr→ : ∀ (Γ : SRC.Ctx SRC.S) →
          SRC.Cstr SRC.S →
          TGT.Type (sorts→ Γ) →
          TGT.Type (sorts→ Γ)
        cstr→ Γ ε σ = σ
        cstr→ Γ (o ∶∶ σ') σ = type→ Γ σ' ⇒ σ
        cstr→ Γ (c₁ # c₂) σ = cstr→ Γ c₂ (cstr→ Γ c₁ σ)

stores→ : ∀ (Γ : SRC.Ctx SRC.S) →
  SRC.Stores SRC.S SRC.s →
  TGT.Stores (sorts→ Γ) (sort→ SRC.s)
stores→ {s = eₛ} Γ σ = type→ Γ σ
stores→ {s = oₛ} Γ _ = `⊤
stores→ {s = σₛ} Γ _ = tt 

ctx→ : (Γ : SRC.Ctx SRC.S) → TGT.Ctx (sorts→ Γ)
ctx→ ∅ = ∅
ctx→ (Γ ▶ x) = (ctx→ Γ) ▶ stores→ Γ x
ctx→ {S ▷ s} (Γ ▸ (o , σ)) = (ctx→ Γ) ▶ type→ Γ σ
 
wk-ope :  ∀ {st : SRC.Stores SRC.S SRC.s} (Γ : SRC.Ctx SRC.S) → SRC.OPE (SRC.dropᵣ SRC.idᵣ) Γ (Γ ▶ st)
wk-ope Γ = ope-drop ope-id

ope→ren : ∀ {ρ : SRC.Ren SRC.S₁ SRC.S₂} (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) → 
  SRC.OPE ρ Γ₁ Γ₂ →
  TGT.Ren (sorts→ Γ₁) (sorts→ Γ₂)
ope→ren Γ Γ ope-id = id
ope→ren (Γ₁ ▶ _) (Γ₂ ▶ _) (ope-keep ope) = TGT.extᵣ (ope→ren Γ₁ Γ₂ ope)
ope→ren Γ₁ (Γ₂ ▶ _) (ope-drop ope) = TGT.dropᵣ (ope→ren Γ₁ Γ₂ ope)
ope→ren (Γ₁ ▸ _) (Γ₂ ▸ _) (ope-keep-inst ope) = TGT.extᵣ (ope→ren Γ₁ Γ₂ ope) 

⊢member→ : (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ρ : SRC.Ren SRC.S₁ SRC.S₂} →
  (ope : SRC.OPE ρ Γ₁ Γ₂) → 
  TGT.OPE (ope→ren Γ₁ Γ₂ ope) (ctx→ Γ₁) (ctx→ Γ₂) →
  (x : SRC.Var SRC.S₁ SRC.s) →
  (ope→ren Γ₁ Γ₂ ope) (member→ Γ₁ x) ≡ member→ Γ₂ (ρ x)   
⊢member→ Γ₁ Γ₂ ope ope→ x = {!   !}

⊢ren→ : (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) {ρ : SRC.Ren SRC.S₁ SRC.S₂} →
  (ope : SRC.OPE ρ Γ₁ Γ₂) → 
  TGT.OPE (ope→ren Γ₁ Γ₂ ope) (ctx→ Γ₁) (ctx→ Γ₂) →
  (σ : SRC.Type SRC.S₁) →
  TGT.ren (ope→ren Γ₁ Γ₂ ope) (type→ Γ₁ σ) ≡ type→ Γ₂ (SRC.ren ρ σ) 
⊢ren→ Γ₁ Γ₂ ope ope→ (` x) = cong `_ (⊢member→ Γ₁ Γ₂ ope ope→ x)
⊢ren→ Γ₁ Γ₂ ope ope→ `⊤ = refl
⊢ren→ Γ₁ Γ₂ ope ope→ (σ₁ ⇒ σ₂) = cong₂ _⇒_ (⊢ren→ Γ₁ Γ₂ ope ope→ σ₁) (⊢ren→ Γ₁ Γ₂ ope ope→ σ₂)
⊢ren→ Γ₁ Γ₂ ope ope→ (SRC.∀`α c ⇒ σ) = cong TGT.∀`α_ {!    !}

⊢ctx→ : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {o} → 
  (ctx→ Γ) ▶ type→ Γ σ ≡ ctx→ (Γ ▸ (o , σ)) 
⊢ctx→ (Γ ▶ x) = refl
⊢ctx→ {S ▷ s} (Γ ▸ (o , σ)) = refl

ope→ : ∀ {ρ : SRC.Ren SRC.S₁ SRC.S₂} (Γ₁ : SRC.Ctx SRC.S₁) (Γ₂ : SRC.Ctx SRC.S₂) → 
  (ope : SRC.OPE ρ Γ₁ Γ₂) → 
  TGT.OPE (ope→ren Γ₁ Γ₂ ope) (ctx→ Γ₁) (ctx→ Γ₂)
ope→ Γ Γ ope-id  = ope-id
ope→ (_▶_ {s = eₛ} Γ₁ σ) (Γ₂ ▶ _) (ope-keep ope) = subst 
  (λ x → TGT.OPE (TGT.extᵣ (ope→ren Γ₁ Γ₂ ope)) (ctx→ Γ₁ TGT.▶ type→ Γ₁ σ) (ctx→ Γ₂ TGT.▶ x)) 
  (⊢ren→ Γ₁ Γ₂ ope (ope→ Γ₁ Γ₂ ope) σ) (ope-keep (ope→ Γ₁ Γ₂ ope))
ope→ (_▶_ {s = oₛ} Γ₁ _) (Γ₂ ▶ _) (ope-keep ope) = ope-keep (ope→ Γ₁ Γ₂ ope)
ope→ (_▶_ {s = σₛ} Γ₁ _) (Γ₂ ▶ _) (ope-keep ope) = ope-keep (ope→ Γ₁ Γ₂ ope)
ope→ Γ₁ (Γ₂ ▶ x) (ope-drop ope) = ope-drop (ope→ Γ₁ Γ₂ ope)
ope→ Γ₁'@(Γ₁ ▸ (o , σ)) Γ₂'@(Γ₂ ▸ (o' , σ')) (ope-keep-inst {ρ} ope) = 
  subst₂ (TGT.OPE (ope→ren Γ₁' Γ₂' (ope-keep-inst ope))) (⊢ctx→ Γ₁) (⊢ctx→ Γ₂) 
    (subst (λ x → TGT.OPE (ope→ren Γ₁' Γ₂' (ope-keep-inst ope)) (ctx→ Γ₁ ▶ type→ Γ₁ σ) (ctx→ Γ₂ ▶ x)) 
      (⊢ren→ Γ₁ Γ₂ ope (ope→ Γ₁ Γ₂ ope) σ) (ope-keep (ope→ Γ₁ Γ₂ ope)))

resolve→ : ∀ (Γ : SRC.Ctx SRC.S) →
  [ SRC.o , SRC.σ ]∈ Γ → 
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ SRC.σ)
resolve→ {S ▷ s} {o} {σ} (Γ SRC.▸ (o , σ)) (here {Γ = Γ}) = {!   !}
resolve→ {S ▷ s} (Γ ▶ σ) (under-bind x) with resolve→ Γ x
resolve→ {S ▷ eₛ} (Γ ▶ σ') (under-bind {σ = σ} x) | t , eq = 
  there t , trans (cong TGT.wk eq) (⊢ren→ Γ (Γ ▶ σ') (wk-ope Γ) (ope→ Γ (Γ ▶ σ') (wk-ope Γ)) σ)
resolve→ {S ▷ oₛ} (Γ ▶ _) (under-bind {σ = σ} x) | t , eq = 
  there t , trans (cong TGT.wk eq) (⊢ren→ Γ (Γ ▶ tt) (wk-ope Γ) {!   !} σ)
resolve→ {S ▷ σₛ} (Γ ▶ σ') (under-bind {σ = σ} x) | t , eq = 
  there t , trans (cong TGT.wk eq) (⊢ren→ Γ (Γ ▶ σ') (wk-ope Γ) (ope→ Γ (Γ SRC.▶ σ') (wk-ope Γ)) σ)
resolve→ {S ▷ s} (Γ ▸ (o , σ')) (under-inst {σ = σ} t) with resolve→ Γ t
... | t , eq = there t , trans (cong TGT.wk eq) {! ⊢ren→ ? ? ? ? ?   !}

var→ : ∀ (Γ : SRC.Ctx SRC.S) {x : SRC.Var SRC.S eₛ} {σ : SRC.Type SRC.S} →
  SRC.wk-ctx Γ x ≡ σ → 
  ∃[ x ] TGT.wk-ctx (ctx→ Γ) x ≡ (type→ Γ σ)
var→ Γ {x} {σ} refl = member→ Γ x , {!   !}

⊢wk : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {σ' : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  (ctx→ Γ TGT.▶ type→ Γ σ) TGT.⊢ e ∶ type→ (Γ SRC.▶ σ) (SRC.wk σ') →
  (ctx→ Γ TGT.▶ type→ Γ σ) TGT.⊢ e ∶ TGT.wk (type→ Γ σ')
⊢wk Γ {σ = σ}  {σ' = σ'} {e = e} ⊢e = subst (λ x → (ctx→ Γ TGT.▶ type→ Γ σ) TGT.⊢ e ∶ x) 
  (sym (⊢ren→ Γ (Γ SRC.▶ σ) (wk-ope Γ) (ope→ Γ (Γ SRC.▶ σ) (wk-ope Γ)) σ')) ⊢e  

⊢Λ→ : ∀ (Γ : SRC.Ctx SRC.S) (c : SRC.Cstr (SRC.S ▷ σₛ)) 
        (e : TGT.Expr (sorts→ ((Γ ▶ tt) SRC.▸* c))) {σ : SRC.Type (SRC.S ▷ σₛ)} →
  ctx→ ((Γ ▶ tt) ▸* c) TGT.⊢ e ∶ type→ ((Γ SRC.▶ tt) SRC.▸* c) σ  →
  ∃[ e ] (ctx→ Γ) TGT.⊢ e ∶ (type→ Γ SRC.σ)
⊢Λ→ Γ ε e ⊢e = (Λ`α→ e) , {! ⊢-Λ ⊢e  !}
⊢Λ→ Γ (c ∶∶ c₁) e ⊢e = {!   !} , {!   !}
⊢Λ→ Γ (c # c₁) e ⊢e = {!   !}  , {!   !}

⊢∶→ : ∀ {Γ : SRC.Ctx SRC.S} →
  Γ SRC.⊢ SRC.t ∶ SRC.σ →
  ∃[ e ] (ctx→ Γ) TGT.⊢ e ∶ (type→ Γ SRC.σ)
⊢∶→ {Γ = Γ} (⊢-`x {x = x} eq) with var→ Γ {x = x} eq
... | x , Γx≡σ = (` x) , ⊢-`x Γx≡σ
⊢∶→ {Γ = Γ} (⊢-`o x) with resolve→ Γ x 
... | x , Γx≡σ = (` x) , ⊢-`x Γx≡σ
⊢∶→ ⊢-⊤ = tt , ⊢-⊤
⊢∶→ {σ = σ} {Γ = Γ} (⊢-λ ⊢e) with ⊢∶→ ⊢e  
... | e , ⊢e = (λ`x→ e) , ⊢-λ (⊢wk Γ ⊢e)
⊢∶→ (⊢-Λ {c = c} ⊢e) with ⊢∶→ ⊢e
... | e→ , ⊢:→e = {!   !} , {!   !}
⊢∶→ (⊢-· ⊢e₁ ⊢e₂) with ⊢∶→ ⊢e₁ | ⊢∶→ ⊢e₂ 
... | e₁ , ⊢e₁ | e₂ , ⊢e₂ = e₁ · e₂ , ⊢-· ⊢e₁ ⊢e₂
⊢∶→ (⊢-• ⊢e ⊢c) with ⊢∶→ ⊢e 
... | e→ , ⊢:→e = {!  !}
⊢∶→ {Γ = Γ} (⊢-let ⊢e₂ ⊢e₁) with ⊢∶→ ⊢e₂ | ⊢∶→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁  = (`let`x= e₂ `in e₁) , ⊢-let ⊢e₂ (⊢wk Γ ⊢e₁)
⊢∶→ {Γ = Γ} (⊢-decl ⊢e) with ⊢∶→ ⊢e
... | e , ⊢e = (`let`x= tt `in e) , ⊢-let ⊢-⊤ {!  ⊢wk Γ ⊢e !}
⊢∶→ {σ = σ} {Γ = Γ} (⊢-inst {o = o} ⊢e₂ ⊢e₁) with ⊢∶→ ⊢e₂ | ⊢∶→ ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢-let ⊢e₂ {!  ⊢wk Γ ⊢e₁  !}
             
{- postulate
  ⊢← : ∀ {Γ : SRC.Ctx SRC.S} →
    (c : SRC.Cstr (SRC.S ▷ σₛ)) →
    (Γ ▶ tt) ▸* c SRC.⊢ SRC.e ∶ SRC.σ →
    (→e : TGT.Expr (sorts→ ((Γ ▶ tt) ▸* c))) →
    (ctx→ ((Γ ▶ tt) ▸* c)) TGT.⊢ →e ∶ type→ {!   !} SRC.σ →
    ∃[ e ] (ctx→ Γ) TGT.⊢ e ∶ type→ {!   !} (SRC.∀`α c ⇒ SRC.σ)

postulate
  ⊢→ : ∀ {Γ : SRC.Ctx SRC.S} →
    Γ SRC.⊢ SRC.e ∶ SRC.∀`α SRC.c ⇒ SRC.σ' →
    Γ SRC.⊢ SRC.c SRC.[ SRC.σ ] →
    (→e : TGT.Expr (sorts→ Γ)) →
    (ctx→ Γ) TGT.⊢ →e ∶ type→ {!   !} (SRC.∀`α SRC.c ⇒ SRC.σ') →
    ∃[ e ] (ctx→ Γ) TGT.⊢ e ∶ type→ {!   !} (SRC.σ' SRC.[ SRC.σ ]) -}

{- ⊢wk :  ∀ (Γ : SRC.Ctx SRC.S) {st : SRC.Stores SRC.S SRC.s} {σ : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  (ctx→ Γ TGT.▶ (stores→ Γ st)) TGT.⊢ e ∶ type→ (Γ SRC.▶ st) (SRC.wk σ) →
  (ctx→ Γ TGT.▶ (stores→ Γ st)) TGT.⊢ e ∶ TGT.wk (type→ Γ σ)
⊢wk Γ {σ = σ} {e = e} ⊢e = subst 
  (λ x → (ctx→ Γ TGT.▶ type→ Γ σ) TGT.⊢ e ∶ x) 
  (sym (⊢ren→ Γ (Γ SRC.▶ σ) (wk→ope Γ) (ope→ Γ (Γ SRC.▶ σ) (wk→ope Γ)) σ)) ⊢e
 -}

{- ⊢wk₁ : ∀ (Γ : SRC.Ctx SRC.S) {σ : SRC.Type SRC.S} {e : TGT.Expr (sorts→ Γ ▷ TGT.eₛ)} →
  (ctx→ Γ TGT.▶ type→ Γ σ) TGT.⊢ e ∶ type→ (Γ SRC.▶ σ) (SRC.wk σ) →
  (ctx→ Γ TGT.▶ type→ Γ σ) TGT.⊢ e ∶ TGT.wk (type→ Γ σ)
⊢wk₁ Γ {σ = σ} {e = e} ⊢e = subst (λ x → (ctx→ Γ TGT.▶ type→ Γ σ) TGT.⊢ e ∶ x) 
  (sym (⊢ren→ Γ (Γ SRC.▶ σ) (wk→ope Γ) (ope→ Γ (Γ SRC.▶ σ) (wk→ope Γ)) σ)) ⊢e
 -}

{- lemma : ∀ {Γ : SRC.Ctx SRC.S} {σ : SRC.Type SRC.S} {o' σ'} → 
  TGT.wk {s' = eₛ} (type→ Γ σ) ≡ type→  (Γ ▸ (o' , σ')) σ
lemma {Γ = Γ} {σ = ` x} = {!   !}
lemma {Γ = Γ} {σ = `⊤} = refl
lemma {Γ = Γ} {σ = σ₁ ⇒ σ₂} = cong₂ _⇒_ lemma lemma
lemma {Γ = Γ} {σ = SRC.∀`α c ⇒ σ'} = cong TGT.∀`α_ {!   !}
 -}

{- ren→ : ∀ {Γ₁ : SRC.Ctx SRC.S₁} {Γ₂ : SRC.Ctx SRC.S₂} → SRC.Ren SRC.S₁ SRC.S₂ → TGT.Ren (sorts→ Γ₁) (sorts→ Γ₂) 
ren→ {Γ₁ = Γ₁ ▶ x₁} {Γ₂ = Γ₂} ρ x = {!   !}
ren→ {Γ₁ = Γ₁ ▸ (o , σ)} {Γ₂ = Γ₂} ρ (here refl) = {!    !}
ren→ {S₁ ▷ s₁} {Γ₁ = Γ₁ ▸ (o , σ)} {Γ₂ = Γ₂} ρ (there x) = ren→ {Γ₁ = Γ₁} {Γ₂ = Γ₂} ρ x
 -}             