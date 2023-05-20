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
ex1 : ‵[] , [] ⊢ num 42 ↓ num 42
ex1 = ↓num

ex2 : ‵[] , [] ⊢ (fun (# 0)) ∙ (num 42) ↓ num 42
ex2 = ↓app ↓fun (↓var here) ↓num

ex3 : ‵[] , [] ⊢ (char 'Z', num 10 , ⟨⟩) ↓ tuple (char 'Z' ∷ num 10 ∷ [])
ex3 = ↓char ↓, ↓num ↓, ↓⟨⟩

ex4 : ‵[] , (numT ∷ []) ∷ [] ⊢ recDecl (numT ∷ []) ⟶ recInst here ↓ rec (num 42 ∷ [])
ex4 = ↓seq ↓recDecl (↓recInst here (↓num ∷ []ᵣ))

ex5 : ‵[] , (charT ∷ charT ∷ numT ∷ []) ∷ [] ⊢ recDecl (charT ∷ charT ∷ numT ∷ []) ⟶ recInst here ↓ rec (char 'A' ∷ char 'B' ∷ num 42 ∷ [])
ex5 = ↓seq ↓recDecl (↓recInst here (↓char ∷ ↓char ∷ ↓num ∷ []ᵣ))
