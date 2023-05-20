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

        γ γ' : Env Γ

        t u : Type
        ts  : List Type

        v  : Value
        vs : List Value

infix  3 _,_⊢_↓_

data _,_⊢_↓_ : Env Γ → (Γᵈ : DataCtx) → (Γ , Γᵈ ⊢ t) → Value → Set

data ReductionResolver (γ : Env Γ) (Γᵈ : DataCtx) : List Type → List Value → Set where
    []ᴿ : ReductionResolver γ Γᵈ [] []
    _∷_ : {e : Γ , Γᵈ ⊢ t} → (γ , Γᵈ ⊢ e ↓ v) → ReductionResolver γ Γᵈ ts vs → ReductionResolver γ Γᵈ (t ∷ ts) (v ∷ vs)

data _,_⊢_↓_ where
    ↓num  : ∀ {n}       → γ , Γᵈ ⊢ num n ↓ num n
    ↓char : ∀ {c}       → γ , Γᵈ ⊢ char c ↓ char c
    ↓var  : (x : t ∈ Γ) → γ , Γᵈ ⊢ var x ↓ γ x
    ↓fun  : {b : t ∷ Γ , Γᵈ ⊢ u}
        ---------------------------
        → γ , Γᵈ ⊢ fun b ↓ clos b γ
    ↓app  : ∀ {s v} {a : Γ , Γᵈ ⊢ t} {b : t ∷ Γ , Γᵈ ⊢ u} {f : Γ , Γᵈ ⊢ t ⇒ u}
        → γ , Γᵈ ⊢ f ↓ clos b γ'
        → v ‵∷ γ' , Γᵈ ⊢ b ↓ s
        → γ , Γᵈ ⊢ a ↓ v
        ----------------------
        → γ , Γᵈ ⊢ (f ∙ a) ↓ s

    -- Tuple
    ↓tuple : {e : TypeResolver Γ Γᵈ ts}
        → ReductionResolver γ Γᵈ ts vs
        ------------------------------
        → γ , Γᵈ ⊢ tuple e ↓ tuple vs
    
    -- Record
    ↓recDecl : γ , ts ∷ Γᵈ ⊢ recDecl ts ↓ unit
    ↓recInst : (x : ts ∈ Γᵈ)
        → ReductionResolver γ Γᵈ ts vs
        -----------------------------
        → γ , Γᵈ ⊢ recInst x ↓ rec vs

    -- Sequence
    ↓seq : {v₁ v₂ : Value} {e₁ : Γ , Γᵈ ⊢ t} {e₂ : Γ , Γᵈ ⊢ u}
        → γ , Γᵈ ⊢ e₁ ↓ v₁
        → γ , Γᵈ ⊢ e₂ ↓ v₂
        -------------------------
        → γ , Γᵈ ⊢ (e₁ ⟶ e₂) ↓ v₂
