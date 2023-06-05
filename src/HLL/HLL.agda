{-
    Language model of the Haskell-like language (HLL).
    The model itself is merely a (minimal) simplified subset of Haskell.
 -}
module HLL.HLL where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.List.Base using (length)

open import HLL.Types
open import HLL.Context using (Ctx)
open import HLL.DataContext using (DataCtx)

open import Utils.Element

private
    variable
        Γ : Ctx
        Γᵈ : DataCtx
        
        t u : Type
        ts : List Type

infix  4 _,_⊢_

data _,_⊢_ : Ctx → DataCtx → Type → Set

data TypeResolver (Γ : Ctx) (Γᵈ : DataCtx) : List Type → Set where
    []ᵀ : TypeResolver Γ Γᵈ []
    _∷_ : (Γ , Γᵈ ⊢ t) → TypeResolver Γ Γᵈ ts → TypeResolver Γ Γᵈ (t ∷ ts) 

data _∈ᵀ_ : (Γ , Γᵈ ⊢ t) → TypeResolver Γ Γᵈ ts → Set where
    here  : {e₁ : Γ , Γᵈ ⊢ t}                   {tr : TypeResolver Γ Γᵈ ts}            → e₁ ∈ᵀ (e₁ ∷ tr)
    there : {e₁ : Γ , Γᵈ ⊢ t} {e₂ : Γ , Γᵈ ⊢ u} {tr : TypeResolver Γ Γᵈ ts} → e₁ ∈ᵀ tr → e₁ ∈ᵀ (e₂ ∷ tr)

data _,_⊢_ where
    num  : ℕ
        ---------------
        → Γ , Γᵈ ⊢ numT
    char : Char
        ----------------
        → Γ , Γᵈ ⊢ charT
    var  : t ∈ Γ
        ------------
        → Γ , Γᵈ ⊢ t
    fun  : t ∷ Γ , Γᵈ ⊢ u
        ----------------
        → Γ , Γᵈ ⊢ t ⇒ u
    _∙_  : Γ , Γᵈ ⊢ t ⇒ u
        → Γ , Γᵈ ⊢ t
        ------------
        → Γ , Γᵈ ⊢ u

    -- Tuple
    tuple : TypeResolver Γ Γᵈ ts
        ------------------------
        → Γ , Γᵈ ⊢ tupleT ts
    
    tLookup : Γ , Γᵈ ⊢ tupleT ts
        → t ∈ ts
        ------------------------
        → Γ , Γᵈ ⊢ t

    -- Record
    recInst : (recDecl ts) ∈ Γᵈ
        → TypeResolver Γ Γᵈ ts
        -----------------------
        → Γ , Γᵈ ⊢ recT ts
    
    rLookup : Γ , Γᵈ ⊢ recT ts
        → t ∈ ts
        ----------------------
        → Γ , Γᵈ ⊢ t
 