{- Examples/test programs for the refactoring of the HLL. -}
module Refactoring.Examples.Refactoring where

open import Agda.Builtin.List
open import Agda.Builtin.Equality

open import HLL.HLL
open import HLL.Types
open import HLL.Context
open import HLL.DataContext

open import Refactoring.Refactoring

open import Utils.Element

-----------------------------------------------------------------------------------------------------------------------------------------------------

hll₁ : [] , [] ⊢ tupleT (numT ∷ numT ∷ [])
hll₁ = tuple (num 42 ∷ num 1337 ∷ []ᵀ)

res₁ : [] , recDecl (numT ∷ numT ∷ []) ∷ [] ⊢ recT (numT ∷ numT ∷ [])
res₁ = recInst here (num 42 ∷ num 1337 ∷ []ᵀ)

ref₁ : (ref hll₁) ≡ res₁
ref₁ = refl

-----------------------------------------------------------------------------------------------------------------------------------------------------

hll₂ : [] , [] ⊢ tupleT (numT ∷ (tupleT (numT ∷ numT ∷ [])) ∷ [])
hll₂ = tuple (num 7 ∷ (tuple (num 42 ∷ num 1337 ∷ []ᵀ)) ∷ []ᵀ)

res₂ : [] , recDecl (numT ∷ recT (numT ∷ numT ∷ []) ∷ []) ∷ recDecl (numT ∷ numT ∷ []) ∷ [] ⊢ recT (numT ∷ (recT (numT ∷ numT ∷ [])) ∷ [])
res₂ = recInst here (num 7 ∷ (recInst (there here) (num 42 ∷ num 1337 ∷ []ᵀ)) ∷ []ᵀ)

ref₂ : (ref hll₂) ≡ res₂
ref₂ = refl

-----------------------------------------------------------------------------------------------------------------------------------------------------
