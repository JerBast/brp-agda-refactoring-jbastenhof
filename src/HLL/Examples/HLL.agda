{-
    Examples/test programs for the HLL.
 -}
module HLL.Examples.HLL where

open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary.Decidable using (True; toWitness)

open import HLL.HLL
open import HLL.Types
open import HLL.Context
open import HLL.DataContext

open import Utils.Element

-- See: https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
#_ : ∀ {Γ : Ctx} {Γᵈ : DataCtx} → (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)} → Γ , Γᵈ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = var (count (toWitness n∈Γ))

-- Examples
ex1 : [] , [] ⊢ tupleT (numT ∷ numT ∷ [])
ex1 = tuple (num 42 ∷ num 1337 ∷ []ᵀ)

ex2 : [] , [] ⊢ tupleT ( (tupleT (numT ∷ numT ∷ [])) ∷ numT ∷ [] )
ex2 = tuple (tuple (num 42 ∷ num 1337 ∷ []ᵀ) ∷ num 7 ∷ []ᵀ)

ex3 : [] , [] ⊢ tupleT ( numT ∷ (tupleT (numT ∷ numT ∷ [])) ∷ [] )
ex3 = tuple (num 7 ∷ (tuple (num 42 ∷ num 1337 ∷ []ᵀ)) ∷ []ᵀ)

ex4 : [] , [] ⊢ tupleT (numT ∷ charT ∷ numT ∷ [])
ex4 = tuple (num 42 ∷ char 'A' ∷ num 1337 ∷ []ᵀ)

ex5 : [] , (numT ∷ []) ∷ [] ⊢ unitT
ex5 = recDecl (numT ∷ [])

ex6 : [] , (numT ∷ charT ∷ numT ∷ []) ∷ [] ⊢ unitT
ex6 = recDecl (numT ∷ charT ∷ numT ∷ [])

ex7 : [] , [] ⊢ numT
ex7 = fun (var here) ∙ num 42

ex8 : [] , (numT ∷ []) ∷ [] ⊢ recT (numT ∷ [])
ex8 = recDecl (numT ∷ []) ⟶ recInst here
