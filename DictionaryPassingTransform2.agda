open import Common using (_▷_; _▷▷_)
open import SystemF
open import SystemO
open import Function.Inverse using (_↔_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)

module DictionaryPassingTransform2 where

module O = SystemO
module F = SystemF

tr-sort : O.Sort O.⊤ᶜ → F.Sort F.⊤ᶜ
tr-sort eₛ = F.eₛ
tr-sort oₛ = F.eₛ
tr-sort τₛ = F.σₛ

tr-sorts : O.Sorts → F.Sorts
tr-sorts [] = []
tr-sorts (S ▷ s) = (tr-sorts S) ▷ tr-sort s

tr-member : O.s ∈ O.S → tr-sort O.s ∈ tr-sorts O.S
tr-member (here refl) = here refl
tr-member (there t) = there (tr-member t)

tr-mono : O.Mono O.S → F.Poly (tr-sorts O.S) 
tr-mono (` x) = ` tr-member x
tr-mono (τ₁ ⇒ τ₂) = tr-mono τ₁ ⇒ tr-mono τ₂

tr-poly : O.Poly O.S → F.Poly (tr-sorts O.S)
tr-poly (O.∀`α o ∶α→ τ ⇒ σ) = F.∀`α (` here refl ⇒ tr-mono τ) ⇒ tr-poly σ
tr-poly (↑ₚ τ) = tr-mono τ

tr-ctx : O.Ctx O.S → F.Ctx (tr-sorts O.S)
tr-ctx {S ▷ eₛ} Γ {eₛ} (here refl) = tr-poly (Γ (here refl))
tr-ctx {S ▷ oₛ} Γ {eₛ} (here refl) = F.`⊤
tr-ctx {S ▷ τₛ} Γ {σₛ} (here refl) = tt
tr-ctx {S ▷ _}  Γ      (there x)   = tr-ctx (ctx-drop Γ) x 

tr :
  O.Γ O.⊢ O.e ∶ O.σ → 
  -------------------------------
  ∃[ e ] (tr-ctx O.Γ) F.⊢ e ∶ (tr-poly O.σ)
tr (⊢-`x {x = x} refl) = ` tr-member x , ⊢-`x {!   !}
tr (⊢-`o {x = x} t) = ` tr-member x , ⊢-`x {!  !}
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
tr (⊢-[τ] {x = x} ⊢e c) with tr ⊢e
tr (⊢-[τ] {τ = τ} {x = x} _ c) | e , ⊢e = (e • tr-mono τ) · ` tr-member x , {!   !}
tr (⊢-∀α ⊢e) with tr ⊢e 
... | e , ⊢e = (Λ`α→ λ`x→ e) , ⊢-Λ (⊢-λ {!   !})