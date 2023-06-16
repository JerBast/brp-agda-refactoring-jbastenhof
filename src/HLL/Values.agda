{- Values and environment for the HLL. -}
module HLL.Values where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import HLL.HLL
open import HLL.Types
open import HLL.Context
open import HLL.DataContext

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        Γ : Ctx
        Γᵈ : DataCtx

        t u : Type
        ts : List Type

-----------------------------------------------------------------------------------------------------------------------------------------------------

data Value : Type → Set

-- Arbitrary list of values of a certain type
data PolyList : List Type → Set where
    []  : PolyList []
    _∷_ : Value t → PolyList ts → PolyList (t ∷ ts)

-- An environment is similar to a PolyList where the type context
-- Γ is the accumulated type sequence
Env : Ctx → Set
Env = PolyList

-- Allowed values within the HLL
data Value where
    num   : ℕ                      → Value numT
    char  : Char                   → Value charT
    clos  : t ∷ Γ , Γᵈ ⊢ u → Env Γ → Value (t ⇒ u)
    tuple : PolyList ts            → Value (tupleT ts)
    rec   : PolyList ts            → Value (recT ts)

-----------------------------------------------------------------------------------------------------------------------------------------------------
