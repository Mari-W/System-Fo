\begin{code}[hide]
open import SystemF
open import SystemFo
open import Data.List using (List; [])
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; subst; sym; subst₂; module ≡-Reasoning)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open ≡-Reasoning

module DictionaryPassingTransform where

module Fᴼ = SystemFo
module F = SystemF

-- Translation --------------------------------------------------------------------------

-- Sorts 

s⇝s : Fᴼ.Sort ⊤ᶜ → F.Sort ⊤ᶜ
s⇝s eₛ = eₛ
s⇝s oₛ = eₛ
s⇝s τₛ = τₛ

Γ⇝S : Fᴼ.Ctx Fᴼ.S → F.Sorts
Γ⇝S  ∅ = []
Γ⇝S (Γ ▸ c) = Γ⇝S Γ ▷ F.eₛ
Γ⇝S {S ▷ s} (Γ ▶ x) = Γ⇝S Γ ▷ s⇝s s

-- Variables

x⇝x :  ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  Fᴼ.Var Fᴼ.S Fᴼ.s → F.Var (Γ⇝S Γ) (s⇝s Fᴼ.s)
x⇝x {Γ = Γ ▶ τ} (here refl) = here refl 
x⇝x {Γ = Γ ▶ τ} (there x) = there (x⇝x x)
x⇝x {Γ = Γ ▸ c} x = there (x⇝x x)

-- Overloaded Variables

o∶τ∈Γ⇝x : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  [ ` Fᴼ.o ∶ Fᴼ.τ ]∈ Γ → F.Var (Γ⇝S Γ) F.eₛ
o∶τ∈Γ⇝x here = here refl
o∶τ∈Γ⇝x (under-bind o∶τ∈Γ) = there (o∶τ∈Γ⇝x o∶τ∈Γ)
o∶τ∈Γ⇝x (under-inst o∶τ∈Γ) = there (o∶τ∈Γ⇝x o∶τ∈Γ)

-- Types  

τ⇝τ : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} →
  Fᴼ.Type Fᴼ.S →
  F.Type (Γ⇝S Γ)
τ⇝τ (` x) = ` x⇝x x
τ⇝τ `⊤ = `⊤
τ⇝τ (τ₁ ⇒ τ₂) = τ⇝τ τ₁ ⇒ τ⇝τ τ₂
τ⇝τ {Γ = Γ} (Fᴼ.∀`α τ) = F.∀`α τ⇝τ {Γ = Γ ▶ ⋆} τ
τ⇝τ ([ o ∶ τ ]⇒ τ') = τ⇝τ τ ⇒ τ⇝τ τ'


T⇝T : ∀ (Γ : Fᴼ.Ctx Fᴼ.S) →
  Fᴼ.Term Fᴼ.S (Fᴼ.kind-of Fᴼ.s) →
  F.Term (Γ⇝S Γ) (F.kind-of (s⇝s Fᴼ.s))
T⇝T {s = eₛ} Γ τ = τ⇝τ τ
T⇝T {s = oₛ} Γ τ = τ⇝τ τ
T⇝T {s = τₛ} Γ _ = ⋆ 

-- Context 

Γ⇝Γ : (Γ : Fᴼ.Ctx Fᴼ.S) → F.Ctx (Γ⇝S Γ)
Γ⇝Γ ∅ = ∅
Γ⇝Γ (Γ ▶ I) = (Γ⇝Γ Γ) ▶ I⇝T I
  where I⇝T : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → Fᴼ.Term Fᴼ.S (item-of Fᴼ.s) → F.Term (Γ⇝S Γ) (F.kind-of (s⇝s Fᴼ.s))
        I⇝T {s = eₛ} τ = τ⇝τ τ
        I⇝T {s = oₛ} ⋆ = `⊤
        I⇝T {s = τₛ} ⋆ = ⋆
Γ⇝Γ (Γ ▸ (` o ∶ τ)) = (Γ⇝Γ Γ) ▶ τ⇝τ τ

-- Terms

⊢t⇝t : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {t : Fᴼ.Term Fᴼ.S Fᴼ.s} {T : Fᴼ.Term Fᴼ.S (Fᴼ.kind-of Fᴼ.s)} →
  Γ Fᴼ.⊢ t ∶ T →
  F.Term (Γ⇝S Γ) (s⇝s Fᴼ.s)
⊢t⇝t (⊢`x {x = x} Γx≡τ) = ` x⇝x x
⊢t⇝t (⊢`o o∶τ∈Γ) = ` o∶τ∈Γ⇝x o∶τ∈Γ
⊢t⇝t ⊢⊤ = tt
⊢t⇝t (⊢λ ⊢e) = λ`x→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢Λ ⊢e) = Λ`α→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢ƛ ⊢e) = λ`x→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢· ⊢e₁ ⊢e₂) = ⊢t⇝t ⊢e₁ · ⊢t⇝t ⊢e₂
⊢t⇝t (⊢• {τ = τ} ⊢e) = ⊢t⇝t ⊢e • (τ⇝τ τ)
⊢t⇝t (⊢⊘ ⊢e o∶τ∈Γ) = ⊢t⇝t ⊢e · ` o∶τ∈Γ⇝x o∶τ∈Γ
⊢t⇝t (⊢let ⊢e₂ ⊢e₁) = let`x= ⊢t⇝t ⊢e₂ `in ⊢t⇝t ⊢e₁
⊢t⇝t (⊢decl ⊢e) = let`x= tt `in  ⊢t⇝t ⊢e
⊢t⇝t (⊢inst ⊢e₂ ⊢e₁) = let`x= ⊢t⇝t ⊢e₂ `in ⊢t⇝t ⊢e₁

-- Renaming 

⊢ρ⇝ρ : ∀ {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂ →
  F.Ren (Γ⇝S Γ₁) (Γ⇝S Γ₂)
⊢ρ⇝ρ ⊢idᵣ = id
⊢ρ⇝ρ (⊢keepᵣ ⊢ρ) = F.extᵣ (⊢ρ⇝ρ ⊢ρ)
⊢ρ⇝ρ (⊢dropᵣ ⊢ρ) = F.dropᵣ (⊢ρ⇝ρ ⊢ρ)
⊢ρ⇝ρ (⊢keep-instᵣ ⊢ρ) = F.extᵣ (⊢ρ⇝ρ ⊢ρ) 
⊢ρ⇝ρ (⊢drop-instᵣ ⊢ρ) = F.dropᵣ (⊢ρ⇝ρ ⊢ρ)

-- Substititution

⊢σ⇝σ : ∀  {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂ →
  F.Sub (Γ⇝S Γ₁) (Γ⇝S Γ₂)
⊢σ⇝σ ⊢idₛ = F.`_
⊢σ⇝σ (⊢keepₛ ⊢σ) = F.extₛ (⊢σ⇝σ ⊢σ)
⊢σ⇝σ (⊢dropₛ ⊢σ) = F.dropₛ (⊢σ⇝σ ⊢σ)
⊢σ⇝σ (⊢typeₛ {τ = τ} ⊢σ) = F.singleₛ (⊢σ⇝σ ⊢σ) (τ⇝τ τ)
⊢σ⇝σ (⊢keep-instₛ ⊢σ) = F.extₛ (⊢σ⇝σ ⊢σ)
⊢σ⇝σ (⊢drop-instₛ ⊢σ) = F.dropₛ (⊢σ⇝σ ⊢σ)

-- Type Preservation --------------------------------------------------------------------

-- Renaming

⊢ρ⇝ρ·x⇝x≡x⇝ρ·x :  {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢ρ : ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (x : Fᴼ.Var Fᴼ.S₁ Fᴼ.s) →
  (⊢ρ⇝ρ ⊢ρ) (x⇝x x) ≡ x⇝x (ρ x)  
⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  ⊢idᵣ x = refl
⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  (⊢keepᵣ ⊢ρ) (here refl) = refl
⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  (⊢keepᵣ ⊢ρ) (there x) = cong there (⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  ⊢ρ x)
⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  (⊢dropᵣ ⊢ρ) x = cong there (⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  ⊢ρ x)
⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  (⊢keep-instᵣ ⊢ρ) x = cong there (⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  ⊢ρ x)
⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  (⊢drop-instᵣ ⊢ρ) x = cong there (⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  ⊢ρ x)

⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ :  {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢ρ : ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (τ : Fᴼ.Type Fᴼ.S₁) →
  F.ren (⊢ρ⇝ρ ⊢ρ) (τ⇝τ τ) ≡ τ⇝τ (Fᴼ.ren ρ τ) 
⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ (` x) = cong `_ (⊢ρ⇝ρ·x⇝x≡x⇝ρ·x  ⊢ρ x)
⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ `⊤ = refl
⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ τ₁) (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ τ₂)
⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ (∀`α τ) = cong F.∀`α_ (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ (⊢keepᵣ ⊢ρ) τ)
⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ ([ ` o ∶ τ ]⇒ τ') = cong₂ _⇒_ (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ τ) (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢ρ τ') 

-- Substititution

⊢σ⇝σ·x⇝x≡τ⇝σ·x  : {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢σ : σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂) → 
  (x : Fᴼ.Var Fᴼ.S₁ τₛ) →
  F.sub (⊢σ⇝σ ⊢σ) (` x⇝x x) ≡ τ⇝τ (Fᴼ.sub σ (` x))
⊢σ⇝σ·x⇝x≡τ⇝σ·x ⊢idₛ x = refl
⊢σ⇝σ·x⇝x≡τ⇝σ·x (⊢keepₛ ⊢σ) (here refl) = refl
⊢σ⇝σ·x⇝x≡τ⇝σ·x (⊢keepₛ {σ = σ} ⊢σ) (there x) = trans 
  (cong F.wk (⊢σ⇝σ·x⇝x≡τ⇝σ·x ⊢σ x)) (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ Fᴼ.⊢wkᵣ (σ x))
⊢σ⇝σ·x⇝x≡τ⇝σ·x (⊢dropₛ {σ = σ} ⊢σ) x  = trans 
  (cong F.wk (⊢σ⇝σ·x⇝x≡τ⇝σ·x ⊢σ x)) (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ Fᴼ.⊢wkᵣ (σ x))
⊢σ⇝σ·x⇝x≡τ⇝σ·x (⊢typeₛ ⊢σ) (here refl) = refl
⊢σ⇝σ·x⇝x≡τ⇝σ·x (⊢typeₛ ⊢σ) (there x) = ⊢σ⇝σ·x⇝x≡τ⇝σ·x ⊢σ x 
⊢σ⇝σ·x⇝x≡τ⇝σ·x (⊢keep-instₛ {σ = σ} ⊢σ) x = trans (cong F.wk (⊢σ⇝σ·x⇝x≡τ⇝σ·x ⊢σ x)) (
   begin 
    F.wk (τ⇝τ (σ x))
  ≡⟨ (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢wk-instᵣ (σ x)) ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ (σ x))
  ≡⟨ cong τ⇝τ (idᵣτ≡τ (σ x)) ⟩ 
    τ⇝τ (σ x)
  ∎)
⊢σ⇝σ·x⇝x≡τ⇝σ·x(⊢drop-instₛ {σ = σ} ⊢σ) x = trans (cong F.wk (⊢σ⇝σ·x⇝x≡τ⇝σ·x ⊢σ x)) (
   begin 
    F.wk (τ⇝τ (σ x))
  ≡⟨ ⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢wk-instᵣ (σ x) ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ (σ x))
  ≡⟨ cong τ⇝τ (idᵣτ≡τ (σ x)) ⟩ 
    τ⇝τ (σ x)
  ∎)

⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ : ∀ {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  (⊢σ : σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂) → 
  (τ : Fᴼ.Type Fᴼ.S₁) →
  F.sub (⊢σ⇝σ ⊢σ) (τ⇝τ τ) ≡ τ⇝τ (Fᴼ.sub σ τ) 
⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ (` x) = ⊢σ⇝σ·x⇝x≡τ⇝σ·x ⊢σ x
⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ `⊤ = refl
⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ τ₁) (⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ  ⊢σ τ₂)
⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ (∀`α τ) = cong F.∀`α_ (⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ (⊢keepₛ ⊢σ) τ)
⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ ([ ` o ∶ τ ]⇒ τ') = cong₂ _⇒_ (⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ τ) (⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢σ τ')

τ'⇝τ'[τ⇝τ]≡τ⇝τ'[τ] : {Γ : Fᴼ.Ctx Fᴼ.S₁} (τ : Fᴼ.Type Fᴼ.S₁) (τ' : Fᴼ.Type (Fᴼ.S₁ ▷ τₛ)) →  
  (τ⇝τ {Γ = Γ ▶ ⋆} τ' F.[ τ⇝τ τ ]) ≡ τ⇝τ (τ' Fᴼ.[ τ ])
τ'⇝τ'[τ⇝τ]≡τ⇝τ'[τ] τ τ' = ⊢σ⇝σ·τ⇝τ≡τ⇝σ·τ ⊢single-typeₛ τ'

-- Type Preserving Translation ----------------------------------------------------------

-- Variables

Γx≡τ⇝Γx≡τ : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {τ : Fᴼ.Type Fᴼ.S} (x : Fᴼ.Var Fᴼ.S eₛ) →
  Fᴼ.lookup Γ x ≡ τ →  
  F.lookup (Γ⇝Γ Γ) (x⇝x x) ≡ (τ⇝τ τ)
Γx≡τ⇝Γx≡τ {Γ = Γ ▶ τ} (here refl) refl = ⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ Fᴼ.⊢wkᵣ τ
Γx≡τ⇝Γx≡τ {Γ = Γ ▶ _} {τ'} (there x) refl = trans 
  (cong F.wk (Γx≡τ⇝Γx≡τ x refl)) 
  (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ Fᴼ.⊢wkᵣ (Fᴼ.lookup Γ x))
Γx≡τ⇝Γx≡τ {Γ = Γ ▸ c@(` o ∶ τ')} {τ} x refl =  (
  begin                     
    F.wk (F.lookup (Γ⇝Γ Γ) (x⇝x x))   
  ≡⟨ cong F.wk (Γx≡τ⇝Γx≡τ x refl) ⟩ 
    F.wk (τ⇝τ τ)
  ≡⟨ ⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢wk-instᵣ τ ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎)

o∶τ∈Γ⇝Γx≡τ : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} →
  (o∶τ∈Γ : [ ` Fᴼ.o ∶ Fᴼ.τ ]∈ Γ) → 
  F.lookup (Γ⇝Γ Γ) (o∶τ∈Γ⇝x o∶τ∈Γ) ≡ (τ⇝τ Fᴼ.τ)
o∶τ∈Γ⇝Γx≡τ {τ = τ} {Γ = Γ Fᴼ.▸ c@(` o ∶ τ)} (here {Γ = Γ}) = 
  begin  
    F.lookup (Γ⇝Γ Γ ▶ τ⇝τ τ) (here refl)
  ≡⟨ ⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢wk-instᵣ τ ⟩
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎
o∶τ∈Γ⇝Γx≡τ {Γ = Γ ▶ _} (under-bind {τ = τ} x) = trans (cong F.wk (o∶τ∈Γ⇝Γx≡τ x)) (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ Fᴼ.⊢wkᵣ τ)
o∶τ∈Γ⇝Γx≡τ {τ = τ} {Γ = Γ ▸ c@(` o ∶ τ')} (under-inst {c' = _ ∶ τ'} o∶τ∈Γ) =
  begin                     
    F.wk (F.lookup (Γ⇝Γ Γ) (o∶τ∈Γ⇝x o∶τ∈Γ))   
  ≡⟨ cong F.wk (o∶τ∈Γ⇝Γx≡τ o∶τ∈Γ) ⟩ 
    F.wk (τ⇝τ τ)
  ≡⟨ ⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢wk-instᵣ τ ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎

-- Terms

τ⇝wk·τ≡wk·τ⇝τ : {Γ : Fᴼ.Ctx Fᴼ.S} {τ' : Fᴼ.Type Fᴼ.S} {I : Fᴼ.Term Fᴼ.S (item-of Fᴼ.s)} → τ⇝τ {Γ = Γ ▶ I} (Fᴼ.wk τ') ≡ F.wk (τ⇝τ τ')
τ⇝wk·τ≡wk·τ⇝τ {τ' = τ'} = sym (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ Fᴼ.⊢wkᵣ τ')

τ⇝wk-inst·τ≡wk-inst·τ⇝τ : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {τ : Fᴼ.Type Fᴼ.S} {τ' : Fᴼ.Type Fᴼ.S} {o} →
  τ⇝τ {Γ = Γ ▸ (` o ∶ τ')} τ ≡ F.wk (τ⇝τ τ)
τ⇝wk-inst·τ≡wk-inst·τ⇝τ  {τ = τ} = 
  begin 
    τ⇝τ τ
  ≡⟨ cong τ⇝τ (sym (idᵣτ≡τ τ)) ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ sym (⊢ρ⇝ρ·τ⇝τ≡τ⇝ρ·τ ⊢wk-instᵣ τ) ⟩ 
    F.wk (τ⇝τ τ)
  ∎
  
⊢t⇝⊢t : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {t : Fᴼ.Term Fᴼ.S Fᴼ.s} {T : Fᴼ.Term Fᴼ.S (Fᴼ.kind-of Fᴼ.s)} →
  (⊢t : Γ Fᴼ.⊢ t ∶ T) →
  (Γ⇝Γ Γ) F.⊢ (⊢t⇝t ⊢t) ∶ (T⇝T Γ T)
⊢t⇝⊢t {Γ = Γ} (⊢`x {x = x} Γxᴼ≡τ) = ⊢`x  (Γx≡τ⇝Γx≡τ x Γxᴼ≡τ)
⊢t⇝⊢t (⊢`o o∶τ∈Γ) = ⊢`x (o∶τ∈Γ⇝Γx≡τ o∶τ∈Γ)
⊢t⇝⊢t ⊢⊤ = ⊢⊤
⊢t⇝⊢t (⊢λ {τ' = τ'} ⊢e) = ⊢λ (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) τ⇝wk·τ≡wk·τ⇝τ (⊢t⇝⊢t ⊢e))
⊢t⇝⊢t (⊢Λ ⊢e) = ⊢Λ (⊢t⇝⊢t ⊢e)
⊢t⇝⊢t (⊢ƛ {c = (` o ∶ τ)} ⊢e) = ⊢λ (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) τ⇝wk-inst·τ≡wk-inst·τ⇝τ (⊢t⇝⊢t ⊢e))
⊢t⇝⊢t (⊢· ⊢e₁ ⊢e₂) = ⊢· (⊢t⇝⊢t ⊢e₁) (⊢t⇝⊢t ⊢e₂)
⊢t⇝⊢t (⊢• {τ' = τ'} {τ = τ} ⊢e) = subst (_ F.⊢  ⊢t⇝t ⊢e • τ⇝τ τ  ∶_) (τ'⇝τ'[τ⇝τ]≡τ⇝τ'[τ] τ τ') (⊢• (⊢t⇝⊢t ⊢e))
⊢t⇝⊢t (⊢⊘ ⊢e o∶τ∈Γ) = ⊢· (⊢t⇝⊢t ⊢e) (⊢`x (o∶τ∈Γ⇝Γx≡τ o∶τ∈Γ))
⊢t⇝⊢t (⊢let ⊢e₂ ⊢e₁) = ⊢let (⊢t⇝⊢t ⊢e₂) (subst (_ F.⊢ ⊢t⇝t ⊢e₁ ∶_) τ⇝wk·τ≡wk·τ⇝τ (⊢t⇝⊢t ⊢e₁))
⊢t⇝⊢t (⊢decl ⊢e) = ⊢let ⊢⊤ (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) τ⇝wk·τ≡wk·τ⇝τ (⊢t⇝⊢t ⊢e))
⊢t⇝⊢t (⊢inst {o = o} ⊢e₂ ⊢e₁) = ⊢let (⊢t⇝⊢t ⊢e₂) (subst (_ F.⊢ ⊢t⇝t ⊢e₁ ∶_) τ⇝wk-inst·τ≡wk-inst·τ⇝τ (⊢t⇝⊢t ⊢e₁))
\end{code}