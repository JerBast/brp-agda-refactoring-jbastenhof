module HLL.Values where

open import Agda.Builtin.Char
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.List.Base

open import HLL.HLL using (_,_⊢_)
open import HLL.Types
open import HLL.Context
open import HLL.DataContext

private
    variable
        Γ : Ctx
        Γᵈ : DataCtx

        t u : Type

-- Declaration of the environments
Env : Ctx → Set
DataEnv : DataCtx → Set

-- Allowed values within the HLL
data Value : Set where
    unit  : Value
    num   : ℕ → Value
    char  : Char → Value
    clos  : t ∷ Γ , Γᵈ ⊢ u → Env Γ → Value
    tuple : List Value → Value
    rec   : List Value → Value

-- Definition of the environments
Env Γ = {t : Type} → t ∈ Γ → Value
DataEnv Γᵈ = {ts : List Type} → ts ∈ Γᵈ → Value

-- Definitions to support extending the environments
‵[] : Env []
‵[] ()

‵[]ᵈ : DataEnv []
‵[]ᵈ ()

infixr 5 _‵∷_
infixr 5 _‵∷ᵈ_

_‵∷_ : ∀ {Γ t} → Value → Env Γ → Env (t ∷ Γ)
(v ‵∷ γ) here      = v
(v ‵∷ γ) (there x) = γ x

-- TODO: I don't think this works as expected...
_‵∷ᵈ_ : ∀ {Γᵈ ts} → Value → DataEnv Γᵈ → DataEnv (ts ∷ Γᵈ)
(v ‵∷ᵈ γᵈ) here      = v
(v ‵∷ᵈ γᵈ) (there x) = γᵈ x
