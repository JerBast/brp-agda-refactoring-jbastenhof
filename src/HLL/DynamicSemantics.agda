module HLL.DynamicSemantics where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.Fin.Base using (toℕ)

open import HLL.HLL
open import HLL.Types
open import HLL.Values
open import HLL.Context using (Ctx)
open import HLL.DataContext using (DataCtx)

open import Utils.Element

private
    variable
        Γ  : Ctx
        Γᵈ : DataCtx

        γ γ' : Env Γ

        t u : Type
        ts  : List Type

        v  : Value
        vs : List Value

        tr : TypeResolver Γ Γᵈ ts

infix  3 _,_⊢_↓_

data _,_⊢_↓_ : Env Γ → (Γᵈ : DataCtx) → (Γ , Γᵈ ⊢ t) → Value → Set

data ReductionResolver (γ : Env Γ) (Γᵈ : DataCtx) : TypeResolver Γ Γᵈ ts → List Value → Set where
    []ᴿ : ReductionResolver γ Γᵈ []ᵀ []
    _∷_ : {e : Γ , Γᵈ ⊢ t} → (γ , Γᵈ ⊢ e ↓ v) → ReductionResolver γ Γᵈ tr vs → ReductionResolver γ Γᵈ (e ∷ tr) (v ∷ vs)

data _,_⊢_↓_ where
    ↓num  : ∀ {n}       → γ , Γᵈ ⊢ num n ↓ num n
    ↓char : ∀ {c}       → γ , Γᵈ ⊢ char c ↓ char c
    ↓var  : {x : t ∈ Γ} → γ , Γᵈ ⊢ var x ↓ γ x
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
    ↓tuple : {tr : TypeResolver Γ Γᵈ ts}
        → ReductionResolver γ Γᵈ tr vs
        ------------------------------
        → γ , Γᵈ ⊢ tuple tr ↓ tuple vs
    
    ↓tLookup : {e : Γ , Γᵈ ⊢ tupleT ts} {x : t ∈ ts} {y : v ∈ vs}
        → γ , Γᵈ ⊢ e ↓ tuple vs
        → toℕ (index x) ≡ toℕ (index y)
        -------------------------------
        → γ , Γᵈ ⊢ (tLookup e x) ↓ v
    
    -- Record
    ↓recInst : {tr : TypeResolver Γ Γᵈ ts} {x : (recDecl ts) ∈ Γᵈ}
        → ReductionResolver γ Γᵈ tr vs
        --------------------------------
        → γ , Γᵈ ⊢ recInst x tr ↓ rec vs

    ↓rLookup : {e : Γ , Γᵈ ⊢ recT ts} {x : t ∈ ts} {y : v ∈ vs}
        → γ , Γᵈ ⊢ e ↓ rec vs
        → toℕ (index x) ≡ toℕ (index y)
        -------------------------------
        → γ , Γᵈ ⊢ (rLookup e x) ↓ v
