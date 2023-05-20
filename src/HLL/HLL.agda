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
        Γ⁰ : DataCtx
        
        t u : Type
        ts : List Type

infix  4 _,_⊢_
infixr 5 _,_

data _,_⊢_ : Ctx → DataCtx → Type → Set where
    num  : ℕ              → Γ , Γ⁰ ⊢ numT
    char : Char           → Γ , Γ⁰ ⊢ charT
    var  : t ∈ Γ          → Γ , Γ⁰ ⊢ t
    fun  : t ∷ Γ , Γ⁰ ⊢ u → Γ , Γ⁰ ⊢ t ⇒ u 
    fix  : t ∷ Γ , Γ⁰ ⊢ t → Γ , Γ⁰ ⊢ t
    _∙_  : Γ , Γ⁰ ⊢ t ⇒ u
        → Γ , Γ⁰ ⊢ t
        ------------
        → Γ , Γ⁰ ⊢ u

    -- Tuple
    ⟨⟩  : Γ , Γ⁰ ⊢ tupleT []
    _,_ : Γ , Γ⁰ ⊢ t
        → Γ , Γ⁰ ⊢ (tupleT ts)
        --------------------------
        → Γ , Γ⁰ ⊢ tupleT (t ∷ ts)

    -- Record
    recDecl : (ts : List Type)
        ---------------------
        → Γ , ts ∷ Γ⁰ ⊢ unitT
    recInst : ts ∈ Γ⁰
        ------------------
        → Γ , Γ⁰ ⊢ recT ts

    -- Sequence
    _⟶_ : Γ , Γ⁰ ⊢ t
        → Γ , Γ⁰ ⊢ u
        ------------
        → Γ , Γ⁰ ⊢ u
