{-
    Language model of the Haskell-like language (HLL).
    The model itself is merely a (minimal) simplified subset of Haskell.
 -}
module HLL.HLL where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import HLL.Types
open import HLL.Context
open import HLL.DataContext

private
    variable
        Γ : Ctx
        Γᵈ : DataCtx
        
        t u : Type
        ts : List Type

infix  4 _,_⊢_
infixr 5 _,_

data _,_⊢_ : Ctx → DataCtx → Type → Set where
    num  : ℕ              → Γ , Γᵈ ⊢ numT
    char : Char           → Γ , Γᵈ ⊢ charT
    var  : t ∈ Γ          → Γ , Γᵈ ⊢ t
    fun  : t ∷ Γ , Γᵈ ⊢ u → Γ , Γᵈ ⊢ t ⇒ u 
    fix  : t ∷ Γ , Γᵈ ⊢ t → Γ , Γᵈ ⊢ t
    _∙_  : Γ , Γᵈ ⊢ t ⇒ u
        → Γ , Γᵈ ⊢ t
        ------------
        → Γ , Γᵈ ⊢ u

    -- Tuple
    ⟨⟩  : Γ , Γᵈ ⊢ tupleT []
    _,_ : Γ , Γᵈ ⊢ t
        → Γ , Γᵈ ⊢ (tupleT ts)
        --------------------------
        → Γ , Γᵈ ⊢ tupleT (t ∷ ts)

    -- Record
    recDecl : (ts : List Type)
        ---------------------
        → Γ , ts ∷ Γᵈ ⊢ unitT
    recInst : ts ∈ Γᵈ
        ------------------
        → Γ , Γᵈ ⊢ recT ts

    -- Sequence
    _⟶_ : Γ , Γᵈ ⊢ t
        → Γ , Γᵈ ⊢ u
        ------------
        → Γ , Γᵈ ⊢ u
