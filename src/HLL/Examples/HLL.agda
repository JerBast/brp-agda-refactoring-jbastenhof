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

-- See: https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
#_ : ∀ {Γ : Ctx} → (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)} → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = var (count (toWitness n∈Γ))

-- Examples
ex1 : [] ⊢ tupleT (numT ∷ numT ∷ [])
ex1 = num 42 , num 1337 , ⟨⟩

ex2 : [] ⊢ tupleT ( (tupleT (numT ∷ numT ∷ [])) ∷ numT ∷ [] )
ex2 = (num 42 , num 1337 , ⟨⟩) , num 7 , ⟨⟩

ex3 : [] ⊢ tupleT ( numT ∷ (tupleT (numT ∷ numT ∷ [])) ∷ [] )
ex3 = num 7 , (num 42 , num 1337 , ⟨⟩) , ⟨⟩

ex4 : [] ⊢ tupleT (numT ∷ charT ∷ numT ∷ [])
ex4 = num 42 , char 'A' , num 1337 , ⟨⟩
