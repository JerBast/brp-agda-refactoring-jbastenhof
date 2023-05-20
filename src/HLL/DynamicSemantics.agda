module HLL.DynamicSemantics where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import HLL.HLL
open import HLL.Types
open import HLL.Values
open import HLL.Context
open import HLL.DataContext

private
    variable
        Γ  : Ctx
        Γᵈ : DataCtx

        γ γ'  : Env Γ
        γᵈ    : DataEnv Γᵈ

        t u   : Type
        v     : Value
        ts    : List Type
        vs    : List Value

infix  3 _,_⊢_↓_
infixr 5 _↓,_

data _,_⊢_↓_ : Env Γ → DataEnv Γᵈ → (Γ , Γᵈ ⊢ t) → Value → Set where
    ↓num  : ∀ {n}       → γ , γᵈ ⊢ num n ↓ num n
    ↓char : ∀ {c}       → γ , γᵈ ⊢ char c ↓ char c
    ↓var  : (x : t ∈ Γ) → γ , γᵈ ⊢ var x ↓ γ x
    ↓fun  : {b : t ∷ Γ , Γᵈ ⊢ u}
        ---------------------------
        → γ , γᵈ ⊢ fun b ↓ clos b γ
    ↓app  : ∀ {s v} {a : Γ , Γᵈ ⊢ t} {b : t ∷ Γ , Γᵈ ⊢ u} {f : Γ , Γᵈ ⊢ t ⇒ u}
        → γ , γᵈ ⊢ f ↓ clos b γ'
        → v ‵∷ γ' , γᵈ ⊢ b ↓ s
        → γ , γᵈ ⊢ a ↓ v
        ----------------------
        → γ , γᵈ ⊢ (f ∙ a) ↓ s

    -- Tuple
    ↓⟨⟩  : γ , γᵈ ⊢ ⟨⟩ ↓ tuple []
    _↓,_ : {e₁ : Γ , Γᵈ ⊢ t} {e₂ : Γ , Γᵈ ⊢ tupleT ts}
        → γ , γᵈ ⊢ e₁ ↓ v
        → γ , γᵈ ⊢ e₂ ↓ tuple vs
        -------------------------------------
        → γ , γᵈ ⊢ (e₁ , e₂) ↓ tuple (v ∷ vs)
    
    -- Record
    ↓recDecl : γ , γᵈ ⊢ recDecl ts ↓ unit
