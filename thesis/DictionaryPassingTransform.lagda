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
\end{code}
\newcommand{\DPTSort}[0]{\begin{code}
s⇝s : Fᴼ.Sort var → F.Sort var
s⇝s eₛ = eₛ
s⇝s oₛ = eₛ
s⇝s τₛ = τₛ
\end{code}}
\newcommand{\DPTSorts}[0]{\begin{code}
Γ⇝S : Fᴼ.Ctx Fᴼ.S → F.Sorts
Γ⇝S  ∅ = []
Γ⇝S (Γ ▸ c) = Γ⇝S Γ ▷ F.eₛ
Γ⇝S {S ▷ s} (Γ ▶ x) = Γ⇝S Γ ▷ s⇝s s
\end{code}}
\begin{code}[hide]
-- Variables
\end{code}
\newcommand{\DPTVar}[0]{\begin{code}
x⇝x :  ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  Fᴼ.Var Fᴼ.S Fᴼ.s → F.Var (Γ⇝S Γ) (s⇝s Fᴼ.s)
x⇝x {Γ = Γ ▶ τ} (here refl) = here refl 
x⇝x {Γ = Γ ▶ τ} (there x) = there (x⇝x x)
x⇝x {Γ = Γ ▸ c} x = there (x⇝x x)
\end{code}}
\begin{code}[hide]
-- Overloaded Variables
\end{code}
\newcommand{\DPTOVar}[0]{\begin{code}
o⇝x : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  [ ` Fᴼ.o ∶ Fᴼ.τ ]∈ Γ → F.Var (Γ⇝S Γ) F.eₛ
o⇝x here = here refl
o⇝x (under-bind o∶τ∈Γ) = there (o⇝x o∶τ∈Γ)
o⇝x (under-cstr o∶τ∈Γ) = there (o⇝x o∶τ∈Γ)
\end{code}}
\begin{code}[hide]
-- Types  
\end{code}
\newcommand{\DPTType}[0]{\begin{code}
τ⇝τ : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} →
  Fᴼ.Type Fᴼ.S →
  F.Type (Γ⇝S Γ)
τ⇝τ ([ o ∶ τ ]⇒ τ') = τ⇝τ τ ⇒ τ⇝τ τ'
-- ...
\end{code}}
\begin{code}[hide]
τ⇝τ (` x) = ` x⇝x x
τ⇝τ `⊤ = `⊤
τ⇝τ (τ₁ ⇒ τ₂) = τ⇝τ τ₁ ⇒ τ⇝τ τ₂
τ⇝τ {Γ = Γ} (Fᴼ.∀`α τ) = F.∀`α τ⇝τ {Γ = Γ ▶ ⋆} τ
\end{code}
\newcommand{\DPTKind}[0]{\begin{code}
T⇝T : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} →
  Fᴼ.Term Fᴼ.S (Fᴼ.type-of Fᴼ.s) →
  F.Term (Γ⇝S Γ) (F.type-of (s⇝s Fᴼ.s))
T⇝T {s = eₛ} τ = τ⇝τ τ
T⇝T {s = oₛ} τ = τ⇝τ τ
T⇝T {s = τₛ} _ = ⋆ 
\end{code}}
\begin{code}[hide]
-- Context 

I⇝T : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → Fᴼ.Term Fᴼ.S (item-of Fᴼ.s) → F.Term (Γ⇝S Γ) (F.type-of (s⇝s Fᴼ.s))
I⇝T {s = eₛ} τ = τ⇝τ τ
I⇝T {s = oₛ} ⋆ = `⊤
I⇝T {s = τₛ} ⋆ = ⋆
\end{code}
\newcommand{\DPTCtx}[0]{\begin{code}
Γ⇝Γ : (Γ : Fᴼ.Ctx Fᴼ.S) → F.Ctx (Γ⇝S Γ)
Γ⇝Γ (Γ ▸ (` o ∶ τ)) = (Γ⇝Γ Γ) ▶ τ⇝τ τ
-- ...
\end{code}}
\begin{code}[hide]
Γ⇝Γ ∅ = ∅
Γ⇝Γ (Γ ▶ I) = (Γ⇝Γ Γ) ▶ I⇝T I

-- Terms
\end{code}
\newcommand{\DPTTerms}[0]{\begin{code}
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
\end{code}}
\begin{code}[hide]
⊢t⇝t (⊢`x {x = x} Γx≡τ) = ` x⇝x x
⊢t⇝t ⊢⊤ = tt
⊢t⇝t (⊢λ ⊢e) = λ`x→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢Λ ⊢e) = Λ`α→ (⊢t⇝t ⊢e)
⊢t⇝t (⊢· ⊢e₁ ⊢e₂) = ⊢t⇝t ⊢e₁ · ⊢t⇝t ⊢e₂
⊢t⇝t (⊢• {τ' = τ'} ⊢e) = ⊢t⇝t ⊢e • (τ⇝τ τ')
⊢t⇝t (⊢let ⊢e₂ ⊢e₁) = let`x= ⊢t⇝t ⊢e₂ `in ⊢t⇝t ⊢e₁

-- Renaming 
\end{code}
\newcommand{\DPTRen}[0]{\begin{code}
⊢ρ⇝ρ : ∀ {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂ →
  F.Ren (Γ⇝S Γ₁) (Γ⇝S Γ₂)
⊢ρ⇝ρ (⊢drop-cstrᵣ ⊢ρ) = F.dropᵣ (⊢ρ⇝ρ ⊢ρ)
-- ...
\end{code}}
\begin{code}[hide]
⊢ρ⇝ρ ⊢idᵣ _ = id
⊢ρ⇝ρ (⊢extᵣ ⊢ρ) = F.extᵣ (⊢ρ⇝ρ ⊢ρ) _
⊢ρ⇝ρ (⊢dropᵣ ⊢ρ) = F.dropᵣ (⊢ρ⇝ρ ⊢ρ)
\end{code}
\begin{code}[hide]
-- Substititution
\end{code}
\newcommand{\DPTSub}[0]{\begin{code}
⊢σ⇝σ : ∀ {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂ →
  F.Sub (Γ⇝S Γ₁) (Γ⇝S Γ₂)
⊢σ⇝σ (⊢single-typeₛ {τ = τ} ⊢σ) = F.singleₛ (⊢σ⇝σ ⊢σ) (τ⇝τ τ)
-- ...
\end{code}}
\begin{code}[hide]
⊢σ⇝σ ⊢idₛ = F.idₛ
⊢σ⇝σ (⊢extₛ ⊢σ) = F.extₛ (⊢σ⇝σ ⊢σ) _ 
⊢σ⇝σ (⊢dropₛ ⊢σ) = F.dropₛ (⊢σ⇝σ ⊢σ)
-- ⊢σ⇝σ (⊢ext-cstrₛ ⊢σ) = F.extₛ (⊢σ⇝σ ⊢σ)
⊢σ⇝σ (⊢drop-cstrₛ ⊢σ) = F.dropₛ (⊢σ⇝σ ⊢σ)
\end{code}
\begin{code}[hide]
-- Type Preservation --------------------------------------------------------------------

-- Renaming
⇝-dist-ren-var : {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢ρ : ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (x : Fᴼ.Var Fᴼ.S₁ Fᴼ.s) →
\end{code}
\newcommand{\DPTVarPresRen}[0]{\begin{code}[inline]
  (⊢ρ⇝ρ ⊢ρ) _ (x⇝x x) ≡ x⇝x (ρ x)  
\end{code}}
\begin{code}[hide]
⇝-dist-ren-var ⊢idᵣ x = refl
⇝-dist-ren-var (⊢extᵣ ⊢ρ) (here refl) = refl
⇝-dist-ren-var (⊢extᵣ ⊢ρ) (there x) = cong there (⇝-dist-ren-var ⊢ρ x)
⇝-dist-ren-var (⊢dropᵣ ⊢ρ) x = cong there (⇝-dist-ren-var ⊢ρ x)
-- ⇝-dist-ren-var (⊢ext-cstrᵣ ⊢ρ) x = cong there (⇝-dist-ren-var ⊢ρ x)
⇝-dist-ren-var (⊢drop-cstrᵣ ⊢ρ) x = cong there (⇝-dist-ren-var ⊢ρ x)
\end{code}
\newcommand{\DPTTypePresRen}[0]{\begin{code}
⇝-dist-ren-type :  {ρ : Fᴼ.Ren Fᴼ.S₁ Fᴼ.S₂} 
                  {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢ρ : ρ Fᴼ.∶ Γ₁ ⇒ᵣ Γ₂) → 
  (τ : Fᴼ.Type Fᴼ.S₁) →
  F.ren (⊢ρ⇝ρ ⊢ρ) (τ⇝τ τ) ≡ τ⇝τ (Fᴼ.ren ρ τ) 
⇝-dist-ren-type ⊢ρ (` x) = cong `_ (⇝-dist-ren-var  ⊢ρ x)
⇝-dist-ren-type ⊢ρ ([ ` o ∶ τ ]⇒ τ') = cong₂ _⇒_ 
  (⇝-dist-ren-type ⊢ρ τ) (⇝-dist-ren-type ⊢ρ τ') 
-- ...
\end{code}}
\begin{code}[hide]
⇝-dist-ren-type ⊢ρ `⊤ = refl
⇝-dist-ren-type ⊢ρ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⇝-dist-ren-type ⊢ρ τ₁) (⇝-dist-ren-type ⊢ρ τ₂)
⇝-dist-ren-type ⊢ρ (∀`α τ) = cong F.∀`α_ (⇝-dist-ren-type (⊢extᵣ ⊢ρ) τ)


⇝-dist-wk-type : {Γ : Fᴼ.Ctx Fᴼ.S} {τ' : Fᴼ.Type Fᴼ.S} {T : Fᴼ.Term Fᴼ.S (item-of Fᴼ.s)} → 
\end{code}
\newcommand{\DPTTypePresWk}[0]{\begin{code}[inline]
  τ⇝τ {Γ = Γ ▶ T} (Fᴼ.wk τ') ≡ F.wk (τ⇝τ τ')
\end{code}}
\begin{code}[hide]
⇝-dist-wk-type{τ' = τ'} = sym (⇝-dist-ren-type Fᴼ.⊢wkᵣ τ')

⇝-dist-wk-inst-type : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {τ : Fᴼ.Type Fᴼ.S} {τ' : Fᴼ.Type Fᴼ.S} {o} →
\end{code}
\newcommand{\DPTTypePresWkInst}[0]{\begin{code}[inline]
  τ⇝τ {Γ = Γ ▸ (` o ∶ τ')} τ ≡ F.wk (τ⇝τ τ)
\end{code}}
\begin{code}[hide]
⇝-dist-wk-inst-type  {τ = τ} = 
  begin 
    τ⇝τ τ
  ≡⟨ cong τ⇝τ (sym (Fᴼ.idᵣτ≡τ τ)) ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ sym (⇝-dist-ren-type ⊢wk-instᵣ τ) ⟩ 
    F.wk (τ⇝τ τ)
  ∎

-- Substititution
\end{code}
\newcommand{\DPTVarPresSub}[0]{\begin{code}
⇝-dist-sub-var : {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} 
                      {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} →
  (⊢σ : σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂) → 
  (x : Fᴼ.Var Fᴼ.S₁ τₛ) →
  F.sub (⊢σ⇝σ ⊢σ) (` x⇝x x) ≡ τ⇝τ (Fᴼ.sub σ (` x))
⇝-dist-sub-var (⊢extₛ ⊢σ) (here refl) = refl
⇝-dist-sub-var (⊢extₛ {σ = σ} ⊢σ) (there x) = trans 
  (cong F.wk (⇝-dist-sub-var ⊢σ x)) (⇝-dist-ren-type Fᴼ.⊢wkᵣ (σ x))
\end{code}}
\begin{code}[hide]
⇝-dist-sub-var ⊢idₛ x = refl
⇝-dist-sub-var (⊢dropₛ {σ = σ} ⊢σ) x  = trans 
  (cong F.wk (⇝-dist-sub-var ⊢σ x)) (⇝-dist-ren-type Fᴼ.⊢wkᵣ (σ x))
⇝-dist-sub-var (⊢single-typeₛ ⊢σ) (here refl) = refl
⇝-dist-sub-var (⊢single-typeₛ ⊢σ) (there x) = ⇝-dist-sub-var ⊢σ x 
⇝-dist-sub-var (⊢drop-cstrₛ {σ = σ} ⊢σ) x = trans (cong F.wk (⇝-dist-sub-var ⊢σ x)) (
   begin 
    F.wk (τ⇝τ (σ x))
  ≡⟨ ⇝-dist-ren-type ⊢wk-instᵣ (σ x) ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ (σ x))
  ≡⟨ cong τ⇝τ (Fᴼ.idᵣτ≡τ (σ x)) ⟩ 
    τ⇝τ (σ x)
  ∎)

⇝-dist-sub-type  : ∀ {σ : Fᴼ.Sub Fᴼ.S₁ Fᴼ.S₂} 
               {Γ₁ : Fᴼ.Ctx Fᴼ.S₁} {Γ₂ : Fᴼ.Ctx Fᴼ.S₂} → 
  (⊢σ : σ Fᴼ.∶ Γ₁ ⇒ₛ Γ₂) → 
  (τ : Fᴼ.Type Fᴼ.S₁) →
\end{code}
\newcommand{\DPTTypePresSub}[0]{\begin{code}[inline]
  F.sub (⊢σ⇝σ ⊢σ) (τ⇝τ τ) ≡ τ⇝τ (Fᴼ.sub σ τ) 
\end{code}}
\begin{code}[hide]
⇝-dist-sub-type  ⊢σ (` x) = ⇝-dist-sub-var ⊢σ x
⇝-dist-sub-type  ⊢σ `⊤ = refl
⇝-dist-sub-type  ⊢σ (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⇝-dist-sub-type  ⊢σ τ₁) (⇝-dist-sub-type   ⊢σ τ₂)
⇝-dist-sub-type  ⊢σ (∀`α τ) = cong F.∀`α_ (⇝-dist-sub-type  (Fᴼ.⊢extₛ ⊢σ) τ)
⇝-dist-sub-type  ⊢σ ([ ` o ∶ τ ]⇒ τ') = cong₂ _⇒_ (⇝-dist-sub-type  ⊢σ τ) (⇝-dist-sub-type  ⊢σ τ')

⇝-dist-τ[τ'] : {Γ : Fᴼ.Ctx Fᴼ.S₁} (τ : Fᴼ.Type Fᴼ.S₁) (τ' : Fᴼ.Type (Fᴼ.S₁ ▷ τₛ)) →  
\end{code}
\newcommand{\DPTTypeDistSingleSub}[0]{\begin{code}[inline]
  (τ⇝τ {Γ = Γ ▶ ⋆} τ' F.[ τ⇝τ τ ]) ≡ τ⇝τ (τ' Fᴼ.[ τ ])
\end{code}}
\newcommand{\DPTTypePresSingleSub}[0]{\begin{code}[inline]
⇝-dist-τ[τ'] τ τ' = ⇝-dist-sub-type  ⊢[] τ'
\end{code}}
\begin{code}[hide]
-- Type Preserving Translation ----------------------------------------------------------

-- Variables
\end{code}
\newcommand{\DPTVarPresLookup}[0]{\begin{code}
⇝-pres-lookup : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} {τ : Fᴼ.Type Fᴼ.S} (x : Fᴼ.Var Fᴼ.S eₛ) →
  Fᴼ.lookup Γ x ≡ τ →  
  F.lookup (Γ⇝Γ Γ) (x⇝x x) ≡ (τ⇝τ τ)
⇝-pres-lookup {Γ = Γ ▶ τ} (here refl) refl = ⇝-dist-ren-type Fᴼ.⊢wkᵣ τ
⇝-pres-lookup {Γ = Γ ▶ _} {τ'} (there x) refl = trans 
  (cong F.wk (⇝-pres-lookup x refl)) 
  (⇝-dist-ren-type Fᴼ.⊢wkᵣ (Fᴼ.lookup Γ x))
-- ...
\end{code}}
\begin{code}[hide]
⇝-pres-lookup {Γ = Γ ▸ c@(` o ∶ τ')} {τ} x refl =  (
  begin                     
    F.wk (F.lookup (Γ⇝Γ Γ) (x⇝x x))   
  ≡⟨ cong F.wk (⇝-pres-lookup x refl) ⟩ 
    F.wk (τ⇝τ τ)
  ≡⟨ ⇝-dist-ren-type ⊢wk-instᵣ τ ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (Fᴼ.idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎)
\end{code}
\newcommand{\DPTOVarPresLookup}[0]{\begin{code}
⇝-pres-cstr-solve : ∀ {Γ : Fᴼ.Ctx Fᴼ.S} → 
  (o∶τ∈Γ : [ ` Fᴼ.o ∶ Fᴼ.τ ]∈ Γ) → 
  F.lookup (Γ⇝Γ Γ) (o⇝x o∶τ∈Γ) ≡ (τ⇝τ Fᴼ.τ)
-- ...
\end{code}}
\begin{code}[hide]
⇝-pres-cstr-solve {τ = τ} {Γ = Γ Fᴼ.▸ c@(` o ∶ τ)} (here {Γ = Γ}) = 
  begin  
    F.lookup (Γ⇝Γ Γ ▶ τ⇝τ τ) (here refl)
  ≡⟨ ⇝-dist-ren-type ⊢wk-instᵣ τ ⟩
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
  ≡⟨ ⇝-dist-ren-type ⊢wk-instᵣ τ ⟩ 
    τ⇝τ (Fᴼ.ren Fᴼ.idᵣ τ)
  ≡⟨ cong τ⇝τ (Fᴼ.idᵣτ≡τ τ) ⟩ 
    τ⇝τ τ
  ∎

-- Terms
\end{code}
\newcommand{\DPTTermPres}[0]{\begin{code}
⇝-pres-⊢ : {Γ : Fᴼ.Ctx Fᴼ.S} {t : Fᴼ.Term Fᴼ.S Fᴼ.s} 
        {T : Fᴼ.Term Fᴼ.S (Fᴼ.type-of Fᴼ.s)} →
  (⊢t : Γ Fᴼ.⊢ t ∶ T) →
  (Γ⇝Γ Γ) F.⊢ (⊢t⇝t ⊢t) ∶ (T⇝T T)
⇝-pres-⊢ (⊢`x {x = x} Γx≡τ) = ⊢`x  (⇝-pres-lookup x Γx≡τ)
⇝-pres-⊢ (⊢`o o∶τ∈Γ) = ⊢`x (⇝-pres-cstr-solve o∶τ∈Γ)
⇝-pres-⊢ (⊢let ⊢e₂ ⊢e₁) = ⊢let (⇝-pres-⊢ ⊢e₂) 
  (subst (_ F.⊢ ⊢t⇝t ⊢e₁ ∶_) ⇝-dist-wk-type(⇝-pres-⊢ ⊢e₁))
⇝-pres-⊢ (⊢ƛ {c = (` o ∶ τ)} ⊢e) = ⊢λ 
  (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) ⇝-dist-wk-inst-type (⇝-pres-⊢ ⊢e))
⇝-pres-⊢ (⊢⊘ ⊢e o∶τ∈Γ) = ⊢· (⇝-pres-⊢ ⊢e) (⊢`x (⇝-pres-cstr-solve o∶τ∈Γ))
⇝-pres-⊢ (⊢• {τ = τ} {τ' = τ'} ⊢e) = subst (_ F.⊢  ⊢t⇝t ⊢e • τ⇝τ τ'  ∶_) 
  (⇝-dist-τ[τ'] τ' τ) (⊢• (⇝-pres-⊢ ⊢e))
-- ...
\end{code}}
\begin{code}[hide]
⇝-pres-⊢ ⊢⊤ = ⊢⊤
⇝-pres-⊢ (⊢λ {τ' = τ'} ⊢e) = ⊢λ (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) 
  ⇝-dist-wk-type(⇝-pres-⊢ ⊢e))
⇝-pres-⊢ (⊢Λ ⊢e) = ⊢Λ (⇝-pres-⊢ ⊢e)
⇝-pres-⊢ (⊢· ⊢e₁ ⊢e₂) = ⊢· (⇝-pres-⊢ ⊢e₁) (⇝-pres-⊢ ⊢e₂)
⇝-pres-⊢ (⊢decl ⊢e) = ⊢let ⊢⊤ (subst (_ F.⊢ ⊢t⇝t ⊢e ∶_) 
  ⇝-dist-wk-type(⇝-pres-⊢ ⊢e))
⇝-pres-⊢ (⊢inst {o = o} ⊢e₂ ⊢e₁) = ⊢let (⇝-pres-⊢ ⊢e₂) 
 (subst (_ F.⊢ ⊢t⇝t ⊢e₁ ∶_) ⇝-dist-wk-inst-type (⇝-pres-⊢ ⊢e₁))
\end{code}
