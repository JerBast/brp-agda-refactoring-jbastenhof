{-
    Examples/test programs for the dynamic semantics.
 -}
module HLL.Examples.DynamicSemantics where

open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary.Decidable using (True; toWitness)

open import HLL.HLL
open import HLL.Types
open import HLL.Values
open import HLL.Context
open import HLL.DataContext
open import HLL.DynamicSemantics

-- See: https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
#_ : ∀ {Γ : Ctx} {Γᵈ : DataCtx} → (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)} → Γ , Γᵈ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = var (count (toWitness n∈Γ))

-- Examples
ex1 : ‵[] , ‵[]ᵈ ⊢ num 42 ↓ num 42
ex1 = ↓num

ex2 : ‵[] , ‵[]ᵈ ⊢ (fun (# 0)) ∙ (num 42) ↓ num 42
ex2 = ↓app ↓fun (↓var here) ↓num

ex3 : ‵[] , ‵[]ᵈ ⊢ (char 'Z', num 10 , ⟨⟩) ↓ tuple (char 'Z' ∷ num 10 ∷ [])
ex3 = ↓char ↓, ↓num ↓, ↓⟨⟩
