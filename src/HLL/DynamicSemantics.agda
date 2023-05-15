module HLL.DynamicSemantics where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import HLL.HLL
open import HLL.Types
open import HLL.Context hiding (lookup)

private
    variable
        Γ : Ctx
        t u : Type

Env : Ctx → Set

data Value : Set where
    num   : ℕ → Value
    char  : Char → Value
    clos  : (t ∷ Γ) ⊢ u → Env Γ → Value
    tuple : List Value → Value

Env Γ = {t : Type} → t ∈ Γ → Value

‵[] : Env []
‵[] ()

infixr 5 _‵∷_

_‵∷_ : ∀ {Γ t} → Value → Env Γ → Env (t ∷ Γ)
(v ‵∷ γ) here      = v
(v ‵∷ γ) (there x) = γ x

private
    variable
        γ γ' : Env Γ

infix 3 _⊢_↓_

data _⊢_↓_ : Env Γ → (Γ ⊢ t) → Value → Set where
    ↓num  : ∀ {n}           → γ ⊢ num n ↓ num n
    ↓char : ∀ {c}           → γ ⊢ char c ↓ char c
    ↓var  : (x : t ∈ Γ)     → γ ⊢ var x ↓ γ x
    ↓fun  : {b : t ∷ Γ ⊢ u} → γ ⊢ fun b ↓ clos b γ
    ↓app  : ∀ {s v} {a : Γ ⊢ t} {b : t ∷ Γ ⊢ u} {f : Γ ⊢ t ⇒ u}
        → γ ⊢ f ↓ clos b γ'
        → v ‵∷ γ' ⊢ b ↓ s
        → γ ⊢ a ↓ v
        -----------------
        → γ ⊢ (f ∙ a) ↓ s

    -- TODO: tuple
