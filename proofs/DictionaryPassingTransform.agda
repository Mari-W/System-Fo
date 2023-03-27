-- [latex] prefix(DPT)
-- [latex] hide
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

-- [latex] block(Sort)

s⇝s : Fᴼ.Sort var → F.Sort var
s⇝s eₛ = eₛ
s⇝s oₛ = eₛ
s⇝s τₛ = τₛ

-- [latex] block(Sorts)

Γ⇝S : Fᴼ.Ctx Fᴼ.S → F.Sorts
Γ⇝S  ∅ = []
Γ⇝S (Γ ▸ c) = Γ⇝S Γ ▷ F.eₛ
Γ⇝S {S ▷ s} (Γ ▶ T) = Γ⇝S Γ ▷ s⇝s s

-- [latex] hide

-- Variables

-- [latex] block(Var)

x⇝x :  ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  Fᴼ.Var Fᴼ.S Fᴼ.s → F.Var (Γ⇝S Γ) (s⇝s Fᴼ.s)
x⇝x {Γ = Γ ▶ τ} (here refl) = here refl 
x⇝x {Γ = Γ ▶ τ} (there x) = there (x⇝x x)
x⇝x {Γ = Γ ▸ c} x = there (x⇝x x)

-- [latex] hide

-- Overloaded Variables

-- [latex] block(OVar)

o⇝x : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  [ ` Fᴼ.o ∶ Fᴼ.τ ]∈ Γ → F.Var (Γ⇝S Γ) F.eₛ
o⇝x here = here refl
o⇝x (under-bind o∶τ∈Γ) = there (o⇝x o∶τ∈Γ)
o⇝x (under-cstr o∶τ∈Γ) = there (o⇝x o∶τ∈Γ)

-- [latex] hide

-- Types  

-- [latex] block(Type)

τ⇝τ : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} →
  Fᴼ.Type Fᴼ.S →
  F.Type (Γ⇝S Γ)
τ⇝τ ([ o ∶ τ ]⇒ τ') = τ⇝τ τ ⇒ τ⇝τ τ'
-- ...
-- [latex] hide
τ⇝τ (` x) = ` x⇝x x
τ⇝τ `⊤ = `⊤
τ⇝τ (τ₁ ⇒ τ₂) = τ⇝τ τ₁ ⇒ τ⇝τ τ₂
τ⇝τ {Γ = Γ} (Fᴼ.∀`α τ) = F.∀`α τ⇝τ {Γ = Γ ▶ ⋆} τ

-- [latex] block(Kind)

T⇝T : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} →
  Fᴼ.Term Fᴼ.S (Fᴼ.type-of Fᴼ.s) →
  F.Term (Γ⇝S Γ) (F.type-of (s⇝s Fᴼ.s))
T⇝T {s = eₛ} τ = τ⇝τ τ
T⇝T {s = oₛ} τ = τ⇝τ τ
T⇝T {s = τₛ} _ = ⋆ 

-- [latex] hide

-- Context 

I⇝T : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → Fᴼ.Term Fᴼ.S (item-of Fᴼ.s) → F.Term (Γ⇝S Γ) (F.type-of (s⇝s Fᴼ.s))
I⇝T {s = eₛ} τ = τ⇝τ τ
I⇝T {s = oₛ} ⋆ = `⊤
I⇝T {s = τₛ} ⋆ = ⋆

-- [latex] block(Ctx)

Γ⇝Γ : (Γ : Fᴼ.Ctx Fᴼ.S) → F.Ctx (Γ⇝S Γ)
Γ⇝Γ (Γ ▸ (` o ∶ τ)) = (Γ⇝Γ Γ) ▶ τ⇝τ τ
-- ...
-- [latex] hide
Γ⇝Γ ∅ = ∅
Γ⇝Γ (Γ ▶ I) = (Γ⇝Γ Γ) ▶ I⇝T I

-- Terms

-- [latex] block(Terms)

⊢t⇝t : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {t : Fᴼ.Term Fᴼ.S Fᴼ.s} 
         {T : Fᴼ.Term Fᴼ.S (Fᴼ.type-of Fᴼ.s)} →
  Γ Fᴼ.⊢ t ∶ T →
  F.Term (Γ⇝S Γ) (s⇝s Fᴼ.s)
⊢t⇝t (⊢`o o∶τ∈Γ) = ` o⇝x o∶τ∈Γ
⊢t⇝t (⊢ƛ ⊢e) = λ`x→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢⊘ ⊢e o∶τ∈Γ) = ⊢t⇝t ⊢e · ` o⇝x o∶τ∈Γ
⊢t⇝t (⊢decl ⊢e) = let`x= tt `in  ⊢t⇝t ⊢e
⊢t⇝t (⊢inst ⊢e₂ ⊢e₁) = let`x= ⊢t⇝t ⊢e₂ `in ⊢t⇝t ⊢e₁
-- ...
-- [latex] hide
⊢t⇝t (⊢`x {x = x} Γx≡τ) = ` x⇝x x
⊢t⇝t ⊢⊤ = tt
⊢t⇝t (⊢λ ⊢e) = λ`x→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢Λ ⊢e) = Λ`α→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢· ⊢e₁ ⊢e₂) = ⊢t⇝t ⊢e₁ · ⊢t⇝t ⊢e₂
⊢t⇝t (⊢• {τ' = τ'} ⊢e) = ⊢t⇝t ⊢e • (τ⇝τ τ')
⊢t⇝t (⊢let ⊢e₂ ⊢e₁) = let`x= ⊢t⇝t ⊢e₂ `in ⊢t⇝t ⊢e₁

-- Renaming 

-- [latex] block(Ren)

⊢ρ⇝ρ : ∀ {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂ →
  F.Ren (Γ⇝S Γ₁) (Γ⇝S Γ₂)
⊢ρ⇝ρ (⊢drop-cstrᵣ ⊢ρ) = F.dropᵣ (⊢ρ⇝ρ ⊢ρ)
-- ...
-- [latex] hide 
⊢ρ⇝ρ ⊢idᵣ _ = id
⊢ρ⇝ρ (⊢extᵣ ⊢ρ) = F.extᵣ (⊢ρ⇝ρ ⊢ρ) _
⊢ρ⇝ρ (⊢dropᵣ ⊢ρ) = F.dropᵣ (⊢ρ⇝ρ ⊢ρ)

-- [latex] hide

-- Substititution

-- [latex] block(Sub)

⊢σ⇝σ : ∀ {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂ →
  F.Sub (Γ⇝S Γ₁) (Γ⇝S Γ₂)
⊢σ⇝σ (⊢single-typeₛ {τ = τ} ⊢σ) = F.singleₛ (⊢σ⇝σ ⊢σ) (τ⇝τ τ)
-- ...
-- [latex] hide 
⊢σ⇝σ ⊢idₛ = F.idₛ
⊢σ⇝σ (⊢extₛ ⊢σ) = F.extₛ (⊢σ⇝σ ⊢σ) _ 
⊢σ⇝σ (⊢dropₛ ⊢σ) = F.dropₛ (⊢σ⇝σ ⊢σ)
-- ⊢σ⇝σ (⊢ext-cstrₛ ⊢σ) = F.extₛ (⊢σ⇝σ ⊢σ)
⊢σ⇝σ (⊢drop-cstrₛ ⊢σ) = F.dropₛ (⊢σ⇝σ ⊢σ)

-- [latex] hide

-- Type Preservation --------------------------------------------------------------------

-- Renaming
⇝-dist-ren-var-type : {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} 
                      {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢ρ : ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (x : Fᴼ.Var Fᴼ.S₁ Fᴼ.s) →
-- [latex] inline(VarPresRen)
  (⊢ρ⇝ρ ⊢ρ) _ (x⇝x x) ≡ x⇝x (ρ x)  
-- [latex] hide
⇝-dist-ren-var-type ⊢idᵣ x = refl
⇝-dist-ren-var-type (⊢extᵣ ⊢ρ) (here refl) = refl
⇝-dist-ren-var-type (⊢extᵣ ⊢ρ) (there x) = cong there (⇝-dist-ren-var-type ⊢ρ x)
⇝-dist-ren-var-type (⊢dropᵣ ⊢ρ) x = cong there (⇝-dist-ren-var-type ⊢ρ x)
-- ⇝-dist-ren-var-type (⊢ext-cstrᵣ ⊢ρ) x = cong there (⇝-dist-ren-var-type ⊢ρ x)
⇝-dist-ren-var-type (⊢drop-cstrᵣ ⊢ρ) x = cong there (⇝-dist-ren-var-type ⊢ρ x)

-- [latex] block(TypePresRen)
⇝-dist-ren-type :  {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} 
                  {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢ρ : ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (τ : Fᴼ.Type Fᴼ.S₁) →
  F.ren (⊢ρ⇝ρ ⊢ρ) (τ⇝τ τ) ≡ τ⇝τ (Fᴼ.ren ρ τ) 
⇝-dist-ren-type ⊢ρ (` x) = cong `_ (⇝-dist-ren-var-type  ⊢ρ x)
⇝-dist-ren-type ⊢ρ ([ ` o ∶ τ ]⇒ τ') = cong₂ _⇒_ 
  (⇝-dist-ren-type ⊢ρ τ) (⇝-dist-ren-type ⊢ρ τ') 
-- ...
-- [latex] hide
⇝-dist-ren-type ⊢ρ `⊤ = refl
⇝-dist-ren-type ⊢ρ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⇝-dist-ren-type ⊢ρ τ₁) (⇝-dist-ren-type ⊢ρ τ₂)
⇝-dist-ren-type ⊢ρ (∀`α τ) = cong F.∀`α_ (⇝-dist-ren-type (⊢extᵣ ⊢ρ) τ)


⇝-dist-wk-type : {Γ : Fᴼ.Ctx Fᴼ.S} {τ' : Fᴼ.Type Fᴼ.S} {T : Fᴼ.Term Fᴼ.S (item-of Fᴼ.s)} → 
-- [latex] inline(TypePresWk)
  τ⇝τ {Γ = Γ ▶ T} (Fᴼ.wk τ') ≡ F.wk (τ⇝τ τ')
-- [latex] hide
⇝-dist-wk-type{τ' = τ'} = sym (⇝-dist-ren-type Fᴼ.⊢wkᵣ τ')

⇝-dist-wk-inst-type : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {τ : Fᴼ.Type Fᴼ.S} {τ' : Fᴼ.Type Fᴼ.S} {o} →
-- [latex] inline(TypePresWkInst)
  τ⇝τ {Γ = Γ ▸ (` o ∶ τ')} τ ≡ F.wk (τ⇝τ τ)
-- [latex] hide
⇝-dist-wk-inst-type  {τ = τ} = 
  begin 
    τ⇝τ τ
  ≡⟨ cong τ⇝τ (sym (Fᴼ.idᵣτ≡τ τ)) ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ sym (⇝-dist-ren-type ⊢wk-cstrᵣ τ) ⟩ 
    F.wk (τ⇝τ τ)
  ∎

-- Substititution

-- [latex] block(VarPresSub)

⇝-dist-sub-var-type : {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} 
                      {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢σ : σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂) → 
  (x : Fᴼ.Var Fᴼ.S₁ τₛ) →
  F.sub (⊢σ⇝σ ⊢σ) (` x⇝x x) ≡ τ⇝τ (Fᴼ.sub σ (` x))
⇝-dist-sub-var-type (⊢extₛ ⊢σ) (here refl) = refl
⇝-dist-sub-var-type (⊢extₛ {σ = σ} ⊢σ) (there x) = trans 
  (cong F.wk (⇝-dist-sub-var-type ⊢σ x)) (⇝-dist-ren-type Fᴼ.⊢wkᵣ (σ x))
-- [latex] hide
⇝-dist-sub-var-type ⊢idₛ x = refl
⇝-dist-sub-var-type (⊢dropₛ {σ = σ} ⊢σ) x  = trans 
  (cong F.wk (⇝-dist-sub-var-type ⊢σ x)) (⇝-dist-ren-type Fᴼ.⊢wkᵣ (σ x))
⇝-dist-sub-var-type (⊢single-typeₛ ⊢σ) (here refl) = refl
⇝-dist-sub-var-type (⊢single-typeₛ ⊢σ) (there x) = ⇝-dist-sub-var-type ⊢σ x 
⇝-dist-sub-var-type (⊢drop-cstrₛ {σ = σ} ⊢σ) x = trans (cong F.wk (⇝-dist-sub-var-type ⊢σ x)) (
   begin 
    F.wk (τ⇝τ (σ x))
  ≡⟨ ⇝-dist-ren-type ⊢wk-cstrᵣ (σ x) ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ (σ x))
  ≡⟨ cong τ⇝τ (Fᴼ.idᵣτ≡τ (σ x)) ⟩ 
    τ⇝τ (σ x)
  ∎)

⇝-dist-sub-type  : ∀ {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} 
               {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  (⊢σ : σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂) → 
  (τ : Fᴼ.Type Fᴼ.S₁) →
-- [latex] inline(TypePresSub)
  F.sub (⊢σ⇝σ ⊢σ) (τ⇝τ τ) ≡ τ⇝τ (Fᴼ.sub σ τ) 
-- [latex] hide
⇝-dist-sub-type  ⊢σ (` x) = ⇝-dist-sub-var-type ⊢σ x
⇝-dist-sub-type  ⊢σ `⊤ = refl
⇝-dist-sub-type  ⊢σ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⇝-dist-sub-type  ⊢σ τ₁) (⇝-dist-sub-type   ⊢σ τ₂)
⇝-dist-sub-type  ⊢σ (∀`α τ) = cong F.∀`α_ (⇝-dist-sub-type  (Fᴼ.⊢extₛ ⊢σ) τ)
⇝-dist-sub-type  ⊢σ ([ ` o ∶ τ ]⇒ τ') = cong₂ _⇒_ (⇝-dist-sub-type  ⊢σ τ) (⇝-dist-sub-type  ⊢σ τ')

⇝-dist-τ[τ'] : {Γ : Fᴼ.Ctx Fᴼ.S₁} (τ : Fᴼ.Type Fᴼ.S₁) (τ' : Fᴼ.Type (Fᴼ.S₁ ▷ τₛ)) →  
-- [latex] inline(TypeDistSingleSub)
  (τ⇝τ {Γ = Γ ▶ ⋆} τ' F.[ τ⇝τ τ ]) ≡ τ⇝τ (τ' Fᴼ.[ τ ])
-- [latex] inline(TypePresSingleSub)
⇝-dist-τ[τ'] τ τ' = ⇝-dist-sub-type  ⊢[] τ'
-- [latex] hide

-- Type Preserving Translation ----------------------------------------------------------

-- Variables

-- [latex] block(VarPresLookup)
⇝-pres-lookup : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {τ : Fᴼ.Type Fᴼ.S} {x : Fᴼ.Var Fᴼ.S eₛ} →
  Fᴼ.lookup Γ x ≡ τ →  
  F.lookup (Γ⇝Γ Γ) (x⇝x x) ≡ (τ⇝τ τ)
⇝-pres-lookup {Γ = Γ ▶ τ} {x = here refl} refl = ⇝-dist-ren-type Fᴼ.⊢wkᵣ τ
⇝-pres-lookup {Γ = Γ ▶ _} {τ'} {x = there x'} refl = trans 
  (cong F.wk (⇝-pres-lookup {x = x'} refl)) 
  (⇝-dist-ren-type Fᴼ.⊢wkᵣ (Fᴼ.lookup Γ x'))
-- ...
-- [latex] hide
⇝-pres-lookup {Γ = Γ ▸ c@(` o ∶ τ')} {τ} {x} refl =  (
  begin                     
    F.wk (F.lookup (Γ⇝Γ Γ) (x⇝x x))   
  ≡⟨ cong F.wk (⇝-pres-lookup refl) ⟩ 
    F.wk (τ⇝τ τ)
  ≡⟨ ⇝-dist-ren-type ⊢wk-cstrᵣ τ ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (Fᴼ.idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎)

-- [latex] block(OVarPresLookup)
⇝-pres-cstr-solve : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  (o∶τ∈Γ : [ ` Fᴼ.o ∶ Fᴼ.τ ]∈ Γ) → 
  F.lookup (Γ⇝Γ Γ) (o⇝x o∶τ∈Γ) ≡ (τ⇝τ Fᴼ.τ)
-- [latex] hide
⇝-pres-cstr-solve {τ = τ} {Γ = Γ Fᴼ.▸ c@(` o ∶ τ)} (here {Γ = Γ}) = 
  begin  
    F.lookup (Γ⇝Γ Γ ▶ τ⇝τ τ) (here refl)
  ≡⟨ ⇝-dist-ren-type ⊢wk-cstrᵣ τ ⟩
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (Fᴼ.idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎
⇝-pres-cstr-solve {Γ = Γ ▶ _} (under-bind {τ = τ} x) = trans 
  (cong F.wk (⇝-pres-cstr-solve x)) 
  (⇝-dist-ren-type Fᴼ.⊢wkᵣ τ)
⇝-pres-cstr-solve {τ = τ} {Γ = Γ ▸ c@(` o ∶ τ')} (under-cstr {c' = _ ∶ τ'} o∶τ∈Γ) =
  begin                     
    F.wk (F.lookup (Γ⇝Γ Γ) (o⇝x o∶τ∈Γ))   
  ≡⟨ cong F.wk (⇝-pres-cstr-solve o∶τ∈Γ) ⟩ 
    F.wk (τ⇝τ τ)
  ≡⟨ ⇝-dist-ren-type ⊢wk-cstrᵣ τ ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (Fᴼ.idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎

-- Terms

-- [latex] block(TermPres)

⇝-pres-⊢ : {Γ : Fᴼ.Ctx Fᴼ.S} {t : Fᴼ.Term Fᴼ.S Fᴼ.s} 
           {T : Fᴼ.Term Fᴼ.S (Fᴼ.type-of Fᴼ.s)} →
  (⊢t : Γ Fᴼ.⊢ t ∶ T) →
  (Γ⇝Γ Γ) F.⊢ (⊢t⇝t ⊢t) ∶ (T⇝T T)
⇝-pres-⊢ (⊢`x Γx≡τ) = ⊢`x  (⇝-pres-lookup Γx≡τ)
⇝-pres-⊢ (⊢`o o∶τ∈Γ) = ⊢`x (⇝-pres-cstr-solve o∶τ∈Γ)
⇝-pres-⊢ (⊢let ⊢e₂ ⊢e₁) = ⊢let (⇝-pres-⊢ ⊢e₂) 
  (subst (_ F.⊢ ⊢t⇝t ⊢e₁ ∶_) ⇝-dist-wk-type(⇝-pres-⊢ ⊢e₁))
⇝-pres-⊢ (⊢ƛ {c = (` o ∶ τ)} ⊢e) = ⊢λ 
  (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) ⇝-dist-wk-inst-type (⇝-pres-⊢ ⊢e))
⇝-pres-⊢ (⊢⊘ ⊢e o∶τ∈Γ) = ⊢· (⇝-pres-⊢ ⊢e) (⊢`x (⇝-pres-cstr-solve o∶τ∈Γ))
⇝-pres-⊢ (⊢• {τ = τ} {τ' = τ'} ⊢e) = subst (_ F.⊢  ⊢t⇝t ⊢e • τ⇝τ τ'  ∶_) 
  (⇝-dist-τ[τ'] τ' τ) (⊢• (⇝-pres-⊢ ⊢e))
-- ...
-- [latex] hide
⇝-pres-⊢ ⊢⊤ = ⊢⊤
⇝-pres-⊢ (⊢λ {τ' = τ'} ⊢e) = ⊢λ (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) 
  ⇝-dist-wk-type(⇝-pres-⊢ ⊢e))
⇝-pres-⊢ (⊢Λ ⊢e) = ⊢Λ (⇝-pres-⊢ ⊢e)
⇝-pres-⊢ (⊢· ⊢e₁ ⊢e₂) = ⊢· (⇝-pres-⊢ ⊢e₁) (⇝-pres-⊢ ⊢e₂)
⇝-pres-⊢ (⊢decl ⊢e) = ⊢let ⊢⊤ (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) 
  ⇝-dist-wk-type(⇝-pres-⊢ ⊢e))
⇝-pres-⊢ (⊢inst {o = o} ⊢e₂ ⊢e₁) = ⊢let (⇝-pres-⊢ ⊢e₂) 
 (subst (_ F.⊢ ⊢t⇝t ⊢e₁ ∶_) ⇝-dist-wk-inst-type (⇝-pres-⊢ ⊢e₁))
-- [latex] end