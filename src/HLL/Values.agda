module HLL.Values where

open import Agda.Builtin.Char
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.List.Base

open import HLL.HLL using (_,_⊢_)
open import HLL.Types
open import HLL.Context
open import HLL.DataContext

open import Utils.Element

private
    variable
        Γ : Ctx
        Γᵈ : DataCtx

        t u : Type

-- Declaration of the environment
Env : Ctx → Set

-- Allowed values within the HLL
data Value : Set where
    num   : ℕ → Value
    char  : Char → Value
    clos  : t ∷ Γ , Γᵈ ⊢ u → Env Γ → Value
    tuple : List Value → Value
    rec   : List Value → Value

-- Definition of the environment
Env Γ = {t : Type} → t ∈ Γ → Value

-- Definitions to support extending the environment
‵[] : Env []
‵[] ()

infixr 5 _‵∷_

_‵∷_ : ∀ {Γ t} → Value → Env Γ → Env (t ∷ Γ)
(v ‵∷ γ) here      = v
(v ‵∷ γ) (there x) = γ x
