{-
    Language model of the Haskell-like language (HLL).
    The model itself is merely a (minimal) simplified subset of Haskell.
 -}
module HLL.HLL where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Char
open import Agda.Builtin.List

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary.Decidable using (True; toWitness)

open import HLL.Types
open import HLL.Context

private
    variable
        n : ℕ
        Γ : Ctx
        t u : Type
        ts : List Type

infix  4 _⊢_
infixr 5 _,_

data _⊢_ : Ctx → Type → Set where
    num  : ℕ                        → Γ ⊢ numT
    char : Char                     → Γ ⊢ charT
    var  : t ∈ Γ                    → Γ ⊢ t
    fun  : t ∷ Γ ⊢ u                → Γ ⊢ t ⇒ u 
    fix  : t ∷ Γ ⊢ t                → Γ ⊢ t
    _∙_  : Γ ⊢ t ⇒ u → Γ ⊢ t        → Γ ⊢ u

    -- Tuple
    ⟨⟩  : Γ ⊢ tupleT []
    _,_ : Γ ⊢ t → Γ ⊢ (tupleT ts)   → Γ ⊢ tupleT (t ∷ ts)

-- See: https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
#_ : (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)} → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = var (count (toWitness n∈Γ))
