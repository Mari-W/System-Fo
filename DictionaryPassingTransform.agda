open import Common using (_▷_; _▷▷_)
open import HindleyMilner
open import SystemO
open import Function.Inverse using (_↔_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)

module DictionaryPassingTransform where

module O = SystemO
module HM = HindleyMilner

tr-sort : O.Sort O.⊤ᶜ → HM.Sort HM.⊤ᶜ
tr-sort eₛ = HM.eₛ
tr-sort oₛ = HM.eₛ
tr-sort τₛ = HM.τₛ

tr-sorts : O.Sorts → HM.Sorts
tr-sorts [] = []
tr-sorts (S ▷ s) = (tr-sorts S) ▷ tr-sort s

tr-member : O.s ∈ O.S → tr-sort O.s ∈ tr-sorts O.S
tr-member (here refl) = here refl
tr-member (there t) = there (tr-member t)

tr-mono : O.Mono O.S → HM.Mono (tr-sorts O.S) 
tr-mono (` x) = ` tr-member x
tr-mono (τ₁ ⇒ τ₂) = tr-mono τ₁ ⇒ tr-mono τ₂

poly-depth : O.Poly O.S → ℕ 
poly-depth (O.∀`α c ⇒ σ) = suc (poly-depth σ)
poly-depth (↑ₚ σ) = zero

ext-by-n : HM.Sorts → ℕ → HM.Sorts 
ext-by-n S zero = S
ext-by-n S (suc n) = ext-by-n (S ▷ τₛ) n

wk-by-n : HM.Mono HM.S → (n : ℕ) → HM.Mono (ext-by-n HM.S n)
wk-by-n τ zero = τ
wk-by-n τ (suc n) = wk-by-n (HM.wk-τ τ) n

reconst-poly : (n : ℕ)  → HM.Mono (ext-by-n (tr-sorts O.S) n) → HM.Poly (tr-sorts O.S)
reconst-poly zero τ = ↑ₚ τ
reconst-poly (suc n) τ = ∀`α reconst-poly n τ

tr-poly' : (σ : O.Poly O.S) → HM.Mono (ext-by-n (tr-sorts O.S) (poly-depth σ)) × HM.Mono (ext-by-n (tr-sorts O.S) (poly-depth σ))
tr-poly' (↑ₚ τ) = HM.`⊤ , tr-mono τ 
tr-poly' (O.∀`α o ∶α→ τ' ⇒ σ) with tr-poly' σ 
... | ` x , τ = wk-by-n (tr-mono τ') (poly-depth σ) , τ -- unreachable
... | `⊤ , τ = wk-by-n (tr-mono τ') (poly-depth σ) , τ
... | τ⇒τ , τ = wk-by-n (tr-mono τ') (poly-depth σ) ⇒ τ⇒τ , τ

tr-poly : O.Poly O.S → HM.Poly (tr-sorts O.S)
tr-poly (↑ₚ τ) = ↑ₚ tr-mono τ
tr-poly σ with tr-poly' σ
... | τ' , τ = reconst-poly (poly-depth σ) (τ' ⇒ τ)

tr-ctx : O.Ctx O.S → HM.Ctx (tr-sorts O.S)
tr-ctx {S ▷ eₛ} Γ {eₛ} (here refl) = tr-poly (Γ (here refl))
tr-ctx {S ▷ oₛ} Γ {eₛ} (here refl) = HM.↑ₚ HM.`⊤
tr-ctx {S ▷ τₛ} Γ {τₛ} (here refl) = tt
tr-ctx {S ▷ _}  Γ      (there x)   = tr-ctx (ctx-drop Γ) x 

tr-cstr : 
  O.Γ O.⊢ᶜ O.c ∶ O.x → 
  -------------------------------
  ∃[ e ] ∃[ τ ] (tr-ctx O.Γ) HM.⊢ e ∶ ↑ₚ τ
tr-cstr (⊢-c {τ = τ} {x = x} e) = ` {!   !} , tr-mono τ , ⊢-`x {!   !}

tr :
  O.Γ O.⊢ O.e ∶ O.σ → 
  -------------------------------
  ∃[ e ] (tr-ctx O.Γ) HM.⊢ e ∶ (tr-poly O.σ)
tr (⊢-`x {x = here refl} refl) = ` (here refl) , ⊢-`x {! refl  !}
tr (⊢-`x {x = there x} refl)   = ` there (tr-member x) , ⊢-`x {!   !}
tr (⊢-`o {x = x} t) = ` tr-member x  , ⊢-`x {!  !}
tr (⊢-λ ⊢e) with tr ⊢e 
... | e , ⊢e = (λ`x→ e) , ⊢-λ {! ⊢e !}
tr (⊢-· ⊢e₁ ⊢e₂) with tr ⊢e₁ | tr ⊢e₂
... | e₁ , ⊢e₁ | e₂ , ⊢e₂ = e₁ · e₂ , ⊢-· ⊢e₁ ⊢e₂
tr (⊢-let ⊢e₂ ⊢e₁) with tr ⊢e₂ | tr ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢-let ⊢e₂ {! ⊢e₁ !}
tr (⊢-decl ⊢e) with tr ⊢e 
... | e , ⊢e = (`let`x= tt `in e) , ⊢-let ⊢-⊤ {! ⊢e !}
tr (⊢-inst ⊢o ⊢e₂ ⊢e₁) with tr ⊢e₂ | tr ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢-let ⊢e₂ {! ⊢e₁ !}
tr (⊢-∀α ⊢e) with tr ⊢e 
... | e , ⊢e = (λ`x→ e) , {! ⊢-∀ ? !}
tr (⊢-[τ] ⊢ᶜc ⊢e) with tr ⊢e | tr-cstr ⊢ᶜc
... | e , ⊢e | e' , σ , ⊢e' = e · e' , ⊢-τ {!  !}

{- tr-e : ∀{Γ : O.Ctx O.S} → Γ O.⊢ O.e ∶ O.σ → HM.Expr (tr-sorts O.S)
tr-e (⊢-`x {x = x} refl) = ` tr-member x
tr-e (⊢-`o {x = x} e) = ` tr-member x
tr-e (⊢-λ e) with tr-e e 
... | e = λ`x→ e
tr-e (⊢-· e₁ e₂) with tr-e e₁ | tr-e e₂
... | e₁ | e₂ = e₁ · e₂
tr-e (⊢-let e₂ e₁) with tr-e e₂ | tr-e e₁ 
... | e₂ | e₁ = `let`x= e₂ `in e₁
tr-e (⊢-decl e) with tr-e e 
... | e = `let`x= tt `in e
tr-e (⊢-inst uq e₂ e₁) with tr-e e₂ | tr-e e₁ 
... | e₂ | e₁ = `let`x= e₂ `in e₁
tr-e (⊢-∀α e) with tr-e e
... | e = λ`x→ e
tr-e (⊢-[τ] c e) with tr-cstr c | tr-e e
... | e' | e = e · e' 
 -}

{- tr-cstr : 
  O.Γ O.⊢ᶜ O.c ∶ O.e → 
  -------------------------------
  ∃[ e ] ∃[ τ ] (tr-ctx O.Γ) HM.⊢ e ∶ ↑ₚ τ
tr-cstr (⊢-c {τ = τ} {x = x} e) = ` {!   !} , tr-mono τ , ⊢-`x {!   !}
 -}
{- tr :
  O.Γ O.⊢ O.e ∶ O.σ → 
  -------------------------------
  ∃[ e ] (tr-ctx O.Γ) HM.⊢ e ∶ (tr-poly O.σ)
tr (⊢-`x {x = here refl} refl) = ` (here refl) , ⊢-`x {! refl  !}
tr (⊢-`x {x = there x} refl)   = ` there (tr-member x) , ⊢-`x {!   !}
tr (⊢-`o {x = x} t) = ` tr-member x  , ⊢-`x {!  !}
tr (⊢-λ ⊢e) with tr ⊢e 
... | e , ⊢e = (λ`x→ e) , ⊢-λ {! ⊢e !}
tr (⊢-· ⊢e₁ ⊢e₂) with tr ⊢e₁ | tr ⊢e₂
... | e₁ , ⊢e₁ | e₂ , ⊢e₂ = e₁ · e₂ , ⊢-· ⊢e₁ ⊢e₂
tr (⊢-let ⊢e₂ ⊢e₁) with tr ⊢e₂ | tr ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢-let ⊢e₂ {! ⊢e₁ !}
tr (⊢-decl ⊢e) with tr ⊢e 
... | e , ⊢e = (`let`x= tt `in e) , ⊢-let ⊢-⊤ {! ⊢e !}
tr (⊢-inst ⊢o ⊢e₂ ⊢e₁) with tr ⊢e₂ | tr ⊢e₁ 
... | e₂ , ⊢e₂ | e₁ , ⊢e₁ = (`let`x= e₂ `in e₁) , ⊢-let ⊢e₂ {! ⊢e₁ !}
tr (⊢-∀α ⊢e) with tr ⊢e 
... | e , ⊢e = (λ`x→ e) , {! ⊢-∀ ? !}
tr (⊢-[τ] ⊢ᶜc ⊢e) with tr ⊢e | tr-cstr ⊢ᶜc
... | e , ⊢e | e' , σ , ⊢e' = e · e' , {!   !} -}



{- tr-cstr : (O.Γ O.⊢ O.c ∶ O.i) → (→Γ HM.⊢ →e ∶ →σ)
tr-cstr (⊢-c {v = v} x) = {!   !} -}

{- data _<_ : (O.Γ O.⊢ O.e ∶ O.σ) → (→Γ HM.⊢ →e ∶ →σ) → Set where -}

{- tr-expr (⊢-`x x) = {!   !}
tr-expr (⊢-λ ⊢e) = {!  ⊢-λ ? !}
tr-expr _ = {!   !} -}
{- tr-expr (⊢-· ⊢e₁ ⊢e₂) = ⊢-· (tr-expr ⊢e₁) (tr-expr ⊢e₂)
tr-expr (⊢-let ⊢e₂ ⊢e₁) = ⊢-let (tr-expr ⊢e₂) (tr-expr ⊢e₁)
tr-expr (⊢-decl ⊢e) = ⊢-let ⊢-⊤ (tr-expr ⊢e)
tr-expr (⊢-inst _ ⊢e₂ ⊢e₁) = ⊢-let (tr-expr ⊢e₂) (tr-expr ⊢e₁)
tr-expr (⊢-∀α ⊢e) = ⊢-∀ (⊢-λ (tr-expr ⊢e))
tr-expr (⊢-[τ] ⊢e ⊢c) = (⊢-· (⊢-τ (tr-expr ⊢e)) (tr-cstr ⊢c)) -}

{- tr-ty : O.Poly O.S → HM.Poly (tr-sorts O.S)
tr-ty a = {!   !}

tr-ctx : O.Ctx O.S → HM.Ctx (tr-sorts O.S) 
tr-ctx {S ▷ eₛ} Γ {eₛ} (here refl) = {! Γ (here refl)   !}
tr-ctx {S ▷ oₛ} Γ {eₛ} (here refl) = HM.`⊤
tr-ctx {S ▷ iₛ} Γ {.(tr-sort O.iₛ)} (here refl) with Γ (here refl)
... | a = {!  tr-ty a  !}
tr-ctx {S ▷ τₛ} Γ {.(tr-sort O.τₛ)} (here refl) = {!   !}
tr-ctx {S ▷ x₁} Γ {s} (there x) = {!   !} -}

{- tr-sort : O.Sort O.⊤ᶜ → HM.Sort HM.⊤ᶜ
tr-sort eₛ = HM.eₛ
tr-sort oₛ = HM.eₛ
tr-sort τₛ = HM.τₛ
tr-sort iₛ = HM.eₛ

tr-sorts : O.Sorts → HM.Sorts
tr-sorts [] = []
tr-sorts (S ▷ eₛ) = (tr-sorts S) ▷ eₛ
tr-sorts (S ▷ oₛ) = tr-sorts S
tr-sorts (S ▷ iₛ) = (tr-sorts S) ▷ eₛ
tr-sorts (S ▷ τₛ) = (tr-sorts S) ▷ τₛ

tr-var : O.Var O.S eₛ → HM.Var (tr-sorts O.S) eₛ 
tr-var (here refl) = here refl
tr-var (there t) with tr-var t 
... | t = {!    !}

tr-ovar : O.Γ O.⊢ ` O.o ∶ O.σ → HM.Var (tr-sorts O.S) eₛ 
tr-ovar (⊢-`o eq el) = {!   !}

tr-ty : O.Poly O.S → HM.Poly (tr-sorts O.S) 
tr-ty σ = {!   !}

tr-ctx : O.Ctx O.S → HM.Ctx (tr-sorts O.S) 
tr-ctx Γ x = {!   !}

tr-cstr : Cstr O.S → HM.Expr (tr-sorts O.S) → HM.Expr (tr-sorts O.S)
tr-cstr ε e = e
tr-cstr (o ∶ τ) e = λ`x→ wk-e e
tr-cstr (c₁ , c₂) e = tr-cstr c₁ (tr-cstr c₂ e)

{- variable
  ~e ~e' ~e'' ~e₁ ~e₂ : HM.Expr (tr-sorts O.S)

infixr 3 _⊢_∶_≻_ 
data _⊢_∶_≻_ : O.Ctx O.S → O.Expr O.S → O.Poly O.S → HM.Expr (tr-sorts O.S) → Set where
  ⊢-`x :  
    O.wk-ctx O.Γ O.x ≡ O.σ →
    ----------------
    O.Γ ⊢ O.` O.x ∶ O.σ ≻ ` (tr-member O.x)
  ⊢-`o :
    (O.σ , O.x) ∈ (O.wk-ctx O.Γ o) →
    ----------------
    O.Γ ⊢ O.` O.x ∶ O.σ ≻ ` (tr-member O.x)
  ⊢-λ : 
    O.Γ O.▶ (O.↑ₚ O.τ₁) ⊢ O.e ∶ O.↑ₚ (O.wk-τ O.τ₂) ≻ HM.e →
    ----------------------------------------------
    O.Γ ⊢ O.λ`x→ O.e ∶ O.↑ₚ (O.τ₁ ⇒ O.τ₂) ≻ HM.λ`x→ HM.e
  ⊢-· : 
    O.Γ ⊢ O.e₁ ∶ O.↑ₚ (O.τ₁ ⇒ O.τ₂) ≻ HM.e₁ →
    O.Γ ⊢ O.e₂ ∶ O.↑ₚ O.τ₁ ≻ HM.e₂ →
    -----------------------
    O.Γ ⊢ O.e₁ O.· O.e₂ ∶ O.↑ₚ O.τ₂ ≻ HM.e₁ HM.· HM.e₂
  ⊢-let : 
    O.Γ ⊢ O.e₂ ∶ O.σ ≻ HM.e₂ →
    O.Γ O.▶ (↑ₚ O.τ) ⊢ O.e₁ ∶ O.↑ₚ (O.wk-τ O.τ) ≻ HM.e₁ →
    ----------------------------
    O.Γ ⊢ O.`let`x= O.e₂ `in O.e₁ ∶ O.↑ₚ O.τ ≻ HM.`let`x= HM.e₂ `in HM.e₁
  ⊢-decl : 
    O.Γ O.▶ O.∅ᶜ ⊢ O.e ∶ O.wk-σ O.σ ≻ HM.e → 
    ---------------------------------
    O.Γ ⊢ O.decl`o`in O.e ∶ O.σ ≻ HM.`let`x= tt `in HM.e
  ⊢-inst :
    Unique O.Γ O.o O.σ →
    O.Γ ⊢ O.e₂ ∶ O.σ ≻ HM.e₂ →
    O.Γ [ O.o ]⊎ O.σ ⊢ O.e₁ ∶ O.↑ₚ (O.wk-τ O.τ) ≻ HM.e₁ →  
    ---------------------------------
    O.Γ ⊢ inst` ` O.o ∶ O.σ `= O.e₂ `in O.e₁ ∶ O.↑ₚ O.τ  ≻ HM.`let`x= HM.e₂ `in HM.e₁
  ⊢-τ :
    O.Γ O.⊢ᶜ O.c O.[ O.τ ] ∶ O.x →
    O.Γ ⊢ O.e ∶ O.∀`α O.c ⇒ O.σ ≻ HM.e →
    -------------------
    O.Γ ⊢ O.e · (` O.x) ∶ (O.σ O.[ O.τ ]) ≻ HM.e · ` (tr-member O.x)
  ⊢-∀ :
    O.Γ ▶ᶜ O.c ⊢ O.e ∶ O.wk-σ O.σ ≻ HM.e → 
    ----------------
    O.Γ ⊢ O.λ`x→ O.e ∶ O.∀`α O.wk-c O.c ⇒ O.wk-σ O.σ ≻ (HM.λ`x→ HM.e)
    
tr : 
  O.Γ ⊢ O.e ∶ O.σ ≻ HM.e → 
  -------------------------------
  (tr-ctx O.Γ) HM.⊢ HM.e ∶ (tr-poly O.σ)
tr (⊢-`x {x = x} refl) =  ⊢-`x {!   !}
tr (⊢-`o {x = x} t) = ⊢-`x {!  !}
tr (⊢-λ ⊢e) with tr ⊢e 
... | ⊢e = ⊢-λ {! ⊢e !}
tr (⊢-· ⊢e₁ ⊢e₂) with tr ⊢e₁ | tr ⊢e₂
... | ⊢e₁ | ⊢e₂ = ⊢-· ⊢e₁ ⊢e₂
tr (⊢-let ⊢e₂ ⊢e₁) with tr ⊢e₂ | tr ⊢e₁ 
... | ⊢e₂ | ⊢e₁ = ⊢-let ⊢e₂ {! ⊢e₁ !}
tr (⊢-decl ⊢e) with tr ⊢e 
... | ⊢e = {!   !}
tr (⊢-inst ⊢o ⊢e₂ ⊢e₁) with tr ⊢e₂ | tr ⊢e₁ 
... | ⊢e₂ | ⊢e₁ = ⊢-let ⊢e₂ {! ⊢e₁ !}
tr (⊢-∀ ⊢e) with tr ⊢e 
... | ⊢e = {! ⊢-∀ ⊢e  !}
tr (⊢-τ ⊢ᶜc ⊢e) with tr ⊢e 
... | ⊢e = {!   !}  -}

infixr 3 _⊢_∶_≻_ 
data _⊢_∶_≻_ : O.Ctx O.S → (t : O.Term O.S O.s) → Types t → HM.Expr (tr-sorts O.S) → Set where
  ⊢-`x :  
    O.wk-ctx O.Γ O.x ≡ O.τ →
    ----------------
    O.Γ ⊢ O.` O.x ∶ O.↑ₚ O.τ ≻ ` (tr-var O.x)
  ⊢-`o :
    (eq : O.wk-ctx O.Γ O.o ≡ O.Σ) →
    (el : O.σ ∈ O.Σ) →
    ----------------
    O.Γ ⊢ O.` o ∶ O.σ ≻ ` (tr-ovar (⊢-`o eq el))
  ⊢-λ : 
    O.Γ O.▶ O.τ₁ ⊢ O.e ∶ O.↑ₚ (O.wk-τ O.τ₂) ≻ HM.e →
    ----------------------------------------------
    O.Γ ⊢ O.λ`x→ O.e ∶ O.↑ₚ (O.τ₁ ⇒ O.τ₂) ≻ HM.λ`x→ HM.e
  ⊢-· : 
    O.Γ ⊢ O.e₁ ∶ O.↑ₚ (O.τ₁ ⇒ O.τ₂) ≻ HM.e₁ →
    O.Γ ⊢ O.e₂ ∶ O.↑ₚ O.τ₁ ≻ HM.e₂ →
    -----------------------
    O.Γ ⊢ O.e₁ O.· O.e₂ ∶ O.↑ₚ O.τ₂ ≻ HM.e₁ HM.· HM.e₂
  ⊢-let : 
    O.Γ ⊢ O.e₂ ∶ O.σ ≻ HM.e₂ →
    O.Γ O.▶ O.τ ⊢ O.e₁ ∶ O.↑ₚ (O.wk-τ O.τ) ≻ HM.e₁ →
    ----------------------------
    O.Γ ⊢ O.`let`x= O.e₂ `in O.e₁ ∶ O.↑ₚ O.τ ≻ HM.`let`x= HM.e₂ `in HM.e₁
  ⊢-decl : 
    O.Γ O.▶ O.∅ᶜ ⊢ O.e ∶ O.wk-σ O.σ ≻ HM.e → 
    ---------------------------------
    O.Γ ⊢ O.decl`o`in O.e ∶ O.σ ≻ HM.e
{-   ⊢-inst :
    O.Γ ⊢ O.e₂ ∶ O.σ ≻ HM.e₂  → 
    (O.Γ [ O.o ]⊎  {!   !}) O.▶ O.σ ⊢ O.e₁ ∶ O.σ' ≻ HM.e₁  → 
    Unique O.Γ O.o O.σ →
    ---------------------------------
    O.Γ ⊢ O.inst` ` O.o ∶ O.σ `= O.e₂ `in O.e₁ ∶ O.σ' ≻ HM.`let`x= HM.e₂ `in HM.e₁ -}
  ⊢-τ :
    O.Γ ⊢ O.e ∶ O.∀`α O.c ⇒ O.σ ≻ HM.e →
    O.Γ ⊢ (O.wk-c O.c O.[ O.τ ]) ∶ tt ≻ HM.e' →
    -------------------
    O.Γ ⊢ O.e ∶ (O.σ O.[ O.τ ]) ≻ HM.e · HM.e'
  ⊢-∀ : 
    (O.Γ O.▶ᶜ O.c) ⊢ O.e ∶ O.σ ≻ HM.e' → 
    ------------------
    O.Γ ⊢ O.e ∶ O.∀`α O.c ⇒ O.wk-σ O.σ ≻ tr-cstr O.c HM.e'


type-preserving-translation :
  O.Γ ⊢ O.e ∶ O.σ ≻ HM.e →
  (tr-ctx O.Γ) HM.⊢ HM.e ∶ (tr-ty O.σ)
type-preserving-translation a = {!   !} -}
{-type-preserving-translation (⊢-`x x) = {!   !}
type-preserving-translation (⊢-λ e) = {!   !}
type-preserving-translation (⊢-· e e₁) = {!   !}
type-preserving-translation (⊢-let e e₁) = {!   !}
type-preserving-translation (⊢-decl e) = {!   !}
type-preserving-translation (⊢-∀ e) = {!   !} 
 -}

{- tr-sort : O.Sort O.⊤ᶜ → HM.Sort HM.⊤ᶜ
tr-sort eₛ = HM.eₛ
tr-sort oₛ = HM.eₛ
tr-sort τₛ = HM.τₛ

tr-sorts : {Γ : O.Γ O.S} → (S : O.Sorts) → HM.Sorts 
tr-sorts [] = []
tr-sorts (S ▷ eₛ) = (tr-sorts S) ▷ eₛ
tr-sorts (S ▷ oₛ) = []
tr-sorts (S ▷ τₛ) = (tr-sorts S) ▷ τₛ

variable 
  ~e ~e' ~e'' ~e₁ ~e₂ : HM.Expr (tr-sorts O.S)
  ~σ : HM.Poly (tr-sorts O.S)

tr-ctx : (Γ : O.Ctx O.S) → HM.Ctx (tr-sorts O.S)
tr-ctx x = λ { v → {!   !} }

tr-c : O.Cstr O.S → HM.Mono (tr-sorts O.S)
tr-c c = {!   !}

c-ty : O.Cstr O.S → O.Mono O.S
c-ty ε = {!   !}
c-ty (c ∶ c₁) = {!   !}
c-ty (c , c₁) = {!   !}

tr-ty : O.Poly O.S → HM.Poly (tr-sorts O.S)
tr-ty (O.∀`α ε ⇒ σ) = HM.∀`α (tr-ty σ)
tr-ty (O.∀`α o ∶ τ ⇒ σ) = {!   !}
tr-ty (O.∀`α c₁ , c₂ ⇒ σ) = {! HM.∀`α (tr-c c₁) ⇒   !}
tr-ty (O.↑ₚ p) = {!   !}

{- var-pres : O.Var O.S O.s → HM.Var (tr-sorts  O.S) (tr-sort O.s)
var-pres {s = eₛ} (here refl) = here refl
var-pres {s = oₛ} (here refl) = {!   !}
var-pres {s = τₛ} (here refl) = here refl
var-pres (there v) = {!   !} -}

infixr 3 _⊢_∶_≻_ 
data _⊢_∶_≻_ : O.Ctx O.S → O.Expr O.S → O.Poly O.S → HM.Expr (tr-sorts O.S) → Set where
  {- ⊢-x : 
    O.wk-ctx O.Γ O.x ≡ O.τ →
    ------------------------
    O.Γ ⊢ O.` O.x ∶ O.↑ₚ O.τ ≻ {!   !} -}
  {- ⊢-λ : 
    O.Γ O.▶ O.τ₁ ⊢ O.e ∶ O.↑ₚ (O.wk-τ O.τ₂) ≻ ~e →
    ----------------------------------------------
    O.Γ ⊢ O.λ`x→ O.e ∶ O.↑ₚ (O.τ₁ ⇒ O.τ₂) ≻ HM.λ`x→ ~e -}
  {- ⊢-· : 
    O.Γ ⊢ O.e₁ ∶ O.↑ₚ (O.τ₁ ⇒ O.τ₂) ≻ HM.e₁ →
    O.Γ ⊢ O.e₂ ∶ O.↑ₚ O.τ₁ ≻ HM.e₂ →
    -----------------------
    O.Γ ⊢ O.e₁ O.· O.e₂ ∶ O.↑ₚ O.τ₂ ≻ HM.e₁ HM.· HM.e₂
  ⊢-let : 
    O.Γ ⊢ O.e₂ ∶ O.σ ≻ HM.e₂ →
    O.Γ O.▶ O.τ ⊢ O.e₁ ∶ O.↑ₚ (O.wk-τ O.τ) ≻ HM.e₁ →
    ----------------------------
    O.Γ ⊢ O.`let`x= O.e₂ `in O.e₁ ∶ O.↑ₚ O.τ ≻ HM.`let`x= HM.e₂ `in HM.e₁ -}
  
{- type-preserving-translation : 
  O.Γ ⊢ O.e ∶ O.σ ≻ ~e →
  -----------------------------
  tr-ctx O.Γ ⊢ ~e ∶ tr-ty O.σ
type-preserving-translation a = {!   !} -}
{- infixr 3 _⊢_∶_≻_
data _⊢_∶_≻_ : Ctxₒ μₒ → μₒ ⊢ₒ eₘₒ → μₒ ⊢ₒ σₘₒ → μₕ ⊢ₕ eₘₕ → Set where
    
→σₕ_ : 
  μₒ ⊢ₒ σₘₒ → 
  μₕ ⊢ₕ σₘₕ
→σₕ a = {!   !}  

→Γₕ_ :
  Ctxₒ μₒ → 
  Ctxₕ μₕ
→Γₕ Γ = {!   !}

→ₕ_ :
  Γₒ ⊢ eₒ ∶ σₒ ≻ eₕ →
  (→Γₕ Γₒ) ⊢ₕ eₕ ∶ {! →σₕ σₒ !}
→ₕ e = {!    !} -}  -}
              