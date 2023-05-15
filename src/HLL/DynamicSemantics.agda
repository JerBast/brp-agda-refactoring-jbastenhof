module HLL.DynamicSemantics where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import HLL.HLL
open import HLL.Types
open import HLL.Values
open import HLL.Context

private
    variable
        Γ     : Ctx
        t u   : Type
        γ γ'  : Env Γ
        v     : Value
        ts    : List Type
        vs    : List Value

infix  3 _⊢_↓_
infixr 5 _↓,_

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

    -- Tuple
    ↓⟨⟩  : γ ⊢ ⟨⟩ ↓ tuple []
    _↓,_ : {e₁ : Γ ⊢ t} {e₂ : Γ ⊢ tupleT ts}
        → γ ⊢ e₁ ↓ v
        → γ ⊢ e₂ ↓ tuple vs
        --------------------------------
        → γ ⊢ (e₁ , e₂) ↓ tuple (v ∷ vs)
