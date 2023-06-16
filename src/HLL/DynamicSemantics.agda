{- Big-step semantics for the HLL. -}
module HLL.DynamicSemantics where

open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import HLL.HLL
open import HLL.Types
open import HLL.BinOp
open import HLL.Values
open import HLL.Context
open import HLL.DataContext

open import Utils.Element

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        Γ  : Ctx
        Γᵈ : DataCtx

        γ γ' : Env Γ

        t u : Type
        ts  : List Type

        op : BinOp

        v  : Value t
        vs : PolyList ts

        tr : TypeResolver Γ Γᵈ ts

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Find the appropriate value for a type lookup in the type context
value-lookup : Env Γ → t ∈ Γ → Value t
value-lookup (v ∷ vs) here      = v
value-lookup (v ∷ vs) (there x) = value-lookup vs x

-- Find the appropriate value for a type lookup in a variadic list
poly-list-lookup : PolyList ts → t ∈ ts → Value t
poly-list-lookup (v ∷ vs) here      = v
poly-list-lookup (v ∷ vs) (there x) = poly-list-lookup vs x

-----------------------------------------------------------------------------------------------------------------------------------------------------

eval-bin-op : BinOp → ℕ → ℕ → ℕ
eval-bin-op add l r = l + r
eval-bin-op mul l r = l * r

-----------------------------------------------------------------------------------------------------------------------------------------------------

infix  3 _,_⊢_⇓_

data _,_⊢_⇓_ : Env Γ → (Γᵈ : DataCtx) → (Γ , Γᵈ ⊢ t) → Value t → Set

-- Accumulate evidence for all elements of a TypeResolver instance
data ReductionResolver (γ : Env Γ) (Γᵈ : DataCtx) : TypeResolver Γ Γᵈ ts → PolyList ts → Set where
    []ᴿ : ReductionResolver γ Γᵈ []ᵀ []
    _∷_ : {e : Γ , Γᵈ ⊢ t} → (γ , Γᵈ ⊢ e ⇓ v) → ReductionResolver γ Γᵈ tr vs → ReductionResolver γ Γᵈ (e ∷ tr) (v ∷ vs)

data _,_⊢_⇓_ where
    ⇓num  : ∀ {n}       → γ , Γᵈ ⊢ num n ⇓ num n
    ⇓char : ∀ {c}       → γ , Γᵈ ⊢ char c ⇓ char c
    ⇓var  : {x : t ∈ Γ} → γ , Γᵈ ⊢ var x ⇓ value-lookup γ x
    ⇓fun  : {b : t ∷ Γ , Γᵈ ⊢ u}
        ---------------------------
        → γ , Γᵈ ⊢ fun b ⇓ clos b γ
    ⇓app  : ∀ {s v} {a : Γ , Γᵈ ⊢ t} {b : t ∷ Γ , Γᵈ ⊢ u} {f : Γ , Γᵈ ⊢ t ⇒ u}
        → γ , Γᵈ ⊢ f ⇓ clos b γ'
        → v ∷ γ' , Γᵈ ⊢ b ⇓ s
        → γ , Γᵈ ⊢ a ⇓ v
        ----------------------
        → γ , Γᵈ ⊢ (f ∙ a) ⇓ s
    
    -- Binary operations
    ⇓bin : ∀ {n₁ n₂} {e₁ : Γ , Γᵈ ⊢ numT} {e₂ : Γ , Γᵈ ⊢ numT}
        → γ , Γᵈ ⊢ e₁ ⇓ num n₁
        → γ , Γᵈ ⊢ e₂ ⇓ num n₂
        ------------------------------------------------------
        → γ , Γᵈ ⊢ (bin op e₁ e₂) ⇓ num (eval-bin-op op n₁ n₂)

    -- Tuple
    ⇓tuple : {tr : TypeResolver Γ Γᵈ ts}
        → ReductionResolver γ Γᵈ tr vs
        ------------------------------
        → γ , Γᵈ ⊢ tuple tr ⇓ tuple vs
    
    ⇓tLookup : {e : Γ , Γᵈ ⊢ tupleT ts} {x : t ∈ ts}
        → γ , Γᵈ ⊢ e ⇓ tuple vs
        ------------------------------------------------
        → γ , Γᵈ ⊢ (tLookup e x) ⇓ poly-list-lookup vs x
    
    -- Record
    ⇓recInst : {tr : TypeResolver Γ Γᵈ ts} {x : (recDecl ts) ∈ Γᵈ}
        → ReductionResolver γ Γᵈ tr vs
        --------------------------------
        → γ , Γᵈ ⊢ recInst x tr ⇓ rec vs

    ⇓rLookup : {e : Γ , Γᵈ ⊢ recT ts} {x : t ∈ ts}
        → γ , Γᵈ ⊢ e ⇓ rec vs
        ------------------------------------------------
        → γ , Γᵈ ⊢ (rLookup e x) ⇓ poly-list-lookup vs x

-----------------------------------------------------------------------------------------------------------------------------------------------------
