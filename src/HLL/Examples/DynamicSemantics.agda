{-
    Examples/test programs for the dynamic semantics.
 -}
module HLL.Examples.DynamicSemantics where

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary.Decidable using (True; toWitness)

open import HLL.HLL
open import HLL.Types
open import HLL.Values
open import HLL.Context
open import HLL.DataContext using (DataCtx)
open import HLL.DynamicSemantics

open import Utils.Element

-- See: https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
#_ : ∀ {Γ : Ctx} {Γᵈ : DataCtx} → (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)} → Γ , Γᵈ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = var (count (toWitness n∈Γ))

-- Examples
ex1 : [] , [] ⊢ num 42 ⇓ num 42
ex1 = ⇓num

ex2 : [] , [] ⊢ (fun (# 0)) ∙ (num 42) ⇓ num 42
ex2 = ⇓app ⇓fun ⇓var ⇓num

ex3 : [] , [] ⊢ tuple (char 'Z' ∷ num 10 ∷ []ᵀ) ⇓ tuple (char 'Z' ∷ num 10 ∷ [])
ex3 = ⇓tuple (⇓char ∷ ⇓num ∷ []ᴿ)

ex4 : [] , recDecl (charT ∷ numT ∷ numT ∷ []) ∷ [] ⊢ recInst here (char 'Z' ∷ num 42 ∷ num 1337 ∷ []ᵀ) ⇓ rec (char 'Z' ∷ num 42 ∷ num 1337 ∷ [])
ex4 = ⇓recInst (⇓char ∷ ⇓num ∷ ⇓num ∷ []ᴿ)

ex5 : [] , [] ⊢ tLookup (tuple (char 'Z' ∷ num 10 ∷ []ᵀ)) (there here) ⇓ num 10
ex5 = ⇓tLookup (⇓tuple (⇓char ∷ ⇓num ∷ []ᴿ))

ex6 : [] , [] ⊢ tLookup (tuple (char 'Z' ∷ num 10 ∷ num 10 ∷ []ᵀ)) (there (there here)) ⇓ num 10
ex6 = ⇓tLookup (⇓tuple (⇓char ∷ ⇓num ∷ ⇓num ∷ []ᴿ))

ex7 : [] , recDecl (charT ∷ numT ∷ numT ∷ []) ∷ [] ⊢ rLookup (recInst here (char 'Z' ∷ num 10 ∷ num 10 ∷ []ᵀ)) (there (there here)) ⇓ num 10
ex7 = ⇓rLookup (⇓recInst (⇓char ∷ ⇓num ∷ ⇓num ∷ []ᴿ))
