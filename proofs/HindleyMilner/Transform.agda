open import Common using (_▷_; _▷▷_)
open import HindleyMilner.Source
open import HindleyMilner.Target
open import Function.Inverse using (_↔_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)

module HindleyMilner.Transform where

module SRC = HindleyMilner.Source
module TGT = HindleyMilner.Target

