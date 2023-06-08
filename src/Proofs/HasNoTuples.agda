{- Proof that after refactoring there are no tuples left. -}
module Proofs.HasNoTuples where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_)

open import HLL.HLL
open import HLL.Types
open import HLL.Context using (Ctx)
open import HLL.DataContext using (DataCtx)

open import Refactoring.Refactoring

open import Utils.Element

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        t u : Type
        ts  : List Type

        Γ  : Ctx
        Γᵈ : DataCtx

-----------------------------------------------------------------------------------------------------------------------------------------------------

data HasNoTuples (Γ : Ctx) (Γᵈ : DataCtx) : Γ , Γᵈ ⊢ t → Set where
    num : ∀ {n}
        → HasNoTuples Γ Γᵈ (num n)
    chr : ∀ {c}
        → HasNoTuples Γ Γᵈ (char c)
    var : {x : t ∈ Γ}
        → HasNoTuples Γ Γᵈ (var x)
    fun : {b : t ∷ Γ , Γᵈ ⊢ u}
        → HasNoTuples Γ Γᵈ (fun b)
    app : {f : Γ , Γᵈ ⊢ t ⇒ u} {a : Γ , Γᵈ ⊢ t}
        → HasNoTuples Γ Γᵈ (f ∙ a)
    rec : {tr : TypeResolver Γ Γᵈ ts} {x : recDecl ts ∈ Γᵈ}
        → HasNoTuples Γ Γᵈ (recInst x tr)
    rlu : {e : Γ , Γᵈ ⊢ recT ts} {x : t ∈ ts}
        → HasNoTuples Γ Γᵈ (rLookup e x)

-----------------------------------------------------------------------------------------------------------------------------------------------------

proof : (e : Γ , Γᵈ ⊢ t) → HasNoTuples (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e ++ Γᵈ)) (ref e)
proof (num n)        = num
proof (char c)       = chr
proof (var x)        = var
proof (fun b)        = fun
proof (f ∙ a)        = app
proof (tuple tr)     = rec
proof (tLookup e x)  = rlu
proof (recInst x tr) = rec
proof (rLookup e x)  = rlu

-----------------------------------------------------------------------------------------------------------------------------------------------------

ex₁ : [] , [] ⊢ tupleT (numT ∷ [])
ex₁ = fun (tuple (num 42 ∷ []ᵀ)) ∙ (char 'A')

p₁ : HasNoTuples [] (recDecl (numT ∷ []) ∷ []) (fun (recInst here (num 42 ∷ []ᵀ)) ∙ (char 'A'))
p₁ = proof ex₁

ex₂ : [] , [] ⊢ charT
ex₂ = fun (fun (tLookup (var here) (there here)) ∙ tuple (num 42 ∷ var here ∷ []ᵀ)) ∙ (char 'A')

p₂ : HasNoTuples [] (recDecl (numT ∷ charT ∷ []) ∷ []) (fun ((fun (rLookup (var here) (there here))) ∙ (recInst here (num 42 ∷ var here ∷ []ᵀ))) ∙ char 'A')
p₂ = proof ex₂

-----------------------------------------------------------------------------------------------------------------------------------------------------
