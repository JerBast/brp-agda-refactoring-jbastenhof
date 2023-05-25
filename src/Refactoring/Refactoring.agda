{- Refactoring for tuples to records. -}
module Refactoring.Refactoring where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.List.Base using (map; _++_; reverse)

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary.Decidable using (True; toWitness)

open import HLL.HLL
open import HLL.Types
open import HLL.Context
open import HLL.DataContext

open import Utils.Element

private
    variable
        t   : Type
        ts  : List Type

        d : Decl

        Γ  : Ctx
        Γᵈ : DataCtx

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Extract the intrinsic type from a syntax term
hll-to-type : Γ , Γᵈ ⊢ t → Type
hll-to-type {t = t} _ = t

-- Extract the types derived from the terms that compose the type resolver
type-resolver-to-type : TypeResolver Γ Γᵈ ts → List Type
type-resolver-to-type {ts = ts} _ = ts

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Eliminate tuples from types
ref-ttr-types : Type → Type

ref-ttr-map-types : List Type → List Type
ref-ttr-map-types []       = []
ref-ttr-map-types (t ∷ ts) = (ref-ttr-types t) ∷ (ref-ttr-map-types ts)

ref-ttr-types numT        = numT
ref-ttr-types charT       = charT
ref-ttr-types unitT       = unitT
ref-ttr-types (t ⇒ u)     = (ref-ttr-types t) ⇒ (ref-ttr-types u)
ref-ttr-types (tupleT ts) = recT (ref-ttr-map-types ts)
ref-ttr-types (recT ts)   = recT (ref-ttr-map-types ts)

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Eliminate tuples from declarations
ref-ttr-decls : Decl → Decl
ref-ttr-decls (recDecl ts) = recDecl (ref-ttr-map-types ts)

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Eliminate tuples from the type context 
ref-ttr-ctx : Ctx → Ctx
ref-ttr-ctx []      = []
ref-ttr-ctx (t ∷ c) = (ref-ttr-types t) ∷ (ref-ttr-ctx c)

-- Ensure that lookups are preserved, but for a different type (in case of a tuple)
ref-ttr-ctx-lookup : t ∈ Γ → (ref-ttr-types t) ∈ (ref-ttr-ctx Γ)
ref-ttr-ctx-lookup here      = here
ref-ttr-ctx-lookup (there x) = there (ref-ttr-ctx-lookup x)

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Eliminate tuples from the declaration context
ref-ttr-data-ctx : DataCtx → DataCtx
ref-ttr-data-ctx []      = []
ref-ttr-data-ctx (d ∷ c) = (ref-ttr-decls d) ∷ (ref-ttr-data-ctx c)

-- Ensure that lookups are preserved, but that declarations might differ (in case of inner tuple type)
ref-ttr-data-ctx-lookup : d ∈ Γᵈ → (ref-ttr-decls d) ∈ (ref-ttr-data-ctx Γᵈ)
ref-ttr-data-ctx-lookup here      = here
ref-ttr-data-ctx-lookup (there x) = there (ref-ttr-data-ctx-lookup x)

-- Ensure that lookups are preserved in extended context, but that declarations might differ (in case of inner tuple type)
ref-ttr-data-ctx-ext-lookup : (Γᵈ' : DataCtx) → d ∈ Γᵈ → (ref-ttr-decls d) ∈ ((ref-ttr-data-ctx Γᵈ) ++ Γᵈ')
ref-ttr-data-ctx-ext-lookup Γᵈ' here      = here
ref-ttr-data-ctx-ext-lookup Γᵈ' (there x) = there (ref-ttr-data-ctx-ext-lookup Γᵈ' x)

-- Create lookup for extended data environment (TODO)
-- postulate ref-ttr-data-ctx-ext-create-lookup : (Γᵈ : DataCtx) → (n : ℕ) → d ∈ Γᵈ

ref-ttr-data-ctx-ext-create-lookup : (Γᵈ : DataCtx) → (n : ℕ) → {n∈Γᵈ : True (suc n ≤? HLL.DataContext.length Γᵈ)} → HLL.DataContext.lookup (toWitness n∈Γᵈ) ∈ Γᵈ
ref-ttr-data-ctx-ext-create-lookup _ n {n∈Γᵈ} = HLL.DataContext.count (toWitness n∈Γᵈ)

ref-ttr-data-ctx-ext-create-rec-decl-lookup : (Γᵈ : DataCtx) → {!   !} → (recDecl ts) ∈ Γᵈ
ref-ttr-data-ctx-ext-create-rec-decl-lookup Γᵈ = {!  !}

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Convert all tuple occurrences to record declarations in pre-order traversal.
-- Note: the result is in reverse order.
ref-ttr-tuple-to-decls : (Γ , Γᵈ ⊢ t) → List Decl

ref-ttr-tuple-to-decls-tr-helper : TypeResolver Γ Γᵈ ts → List Decl
ref-ttr-tuple-to-decls-tr-helper []ᵀ      = []
ref-ttr-tuple-to-decls-tr-helper (e ∷ tr) = (ref-ttr-tuple-to-decls e) ++ (ref-ttr-tuple-to-decls-tr-helper tr)

ref-ttr-tuple-to-decls (num n)        = []
ref-ttr-tuple-to-decls (char c)       = []
ref-ttr-tuple-to-decls (var x)        = []
ref-ttr-tuple-to-decls (fun b)        = ref-ttr-tuple-to-decls b
ref-ttr-tuple-to-decls (f ∙ a)        = (ref-ttr-tuple-to-decls f) ++ (ref-ttr-tuple-to-decls a)
ref-ttr-tuple-to-decls (tuple tr)     = (recDecl (ref-ttr-map-types (type-resolver-to-type tr))) ∷ (ref-ttr-tuple-to-decls-tr-helper tr)
ref-ttr-tuple-to-decls (recInst x tr) = ref-ttr-tuple-to-decls-tr-helper tr

ref-ttr-ttd-extend-data-ctx : (e : Γ , Γᵈ ⊢ t) → DataCtx
ref-ttr-ttd-extend-data-ctx {Γᵈ = Γᵈ} e = Γᵈ ++ (reverse (ref-ttr-tuple-to-decls e))

-- TODO: Make more efficient?
ref-ttr-tuple-remaining-cnt : (Γ , Γᵈ ⊢ t) → ℕ
ref-ttr-tuple-remaining-cnt e = Data.List.Base.length (ref-ttr-tuple-to-decls e)

-----------------------------------------------------------------------------------------------------------------------------------------------------

ref-ttr-helper : (Γᵈ' : DataCtx) → ℕ → (e : Γ , Γᵈ ⊢ t) → ((ref-ttr-ctx Γ) , ((ref-ttr-data-ctx Γᵈ) ++ Γᵈ') ⊢ (ref-ttr-types t))

ref-ttr-helper-tr-helper : (Γᵈ' : DataCtx) → ℕ → TypeResolver Γ Γᵈ ts → TypeResolver (ref-ttr-ctx Γ) ((ref-ttr-data-ctx Γᵈ) ++ Γᵈ') (ref-ttr-map-types ts)
ref-ttr-helper-tr-helper Γᵈ' idx []ᵀ      = []ᵀ
ref-ttr-helper-tr-helper Γᵈ' idx (e ∷ tr) = (ref-ttr-helper Γᵈ' idx e) ∷ (ref-ttr-helper-tr-helper Γᵈ' (idx + (ref-ttr-tuple-remaining-cnt e)) tr)

ref-ttr-helper           Γᵈ' idx (num n)        = num n
ref-ttr-helper           Γᵈ' idx (char c)       = char c
ref-ttr-helper           Γᵈ' idx (var x)        = var (ref-ttr-ctx-lookup x)
ref-ttr-helper           Γᵈ' idx (fun b)        = fun (ref-ttr-helper Γᵈ' idx b)
ref-ttr-helper           Γᵈ' idx e@(f ∙ a)      = (ref-ttr-helper Γᵈ' idx f) ∙ (ref-ttr-helper Γᵈ' (idx + (ref-ttr-tuple-remaining-cnt e)) a)
ref-ttr-helper {Γᵈ = Γᵈ} Γᵈ' idx (tuple tr)     = recInst {!   !} (ref-ttr-helper-tr-helper Γᵈ' (suc idx) tr)
-- ref-ttr-helper {Γᵈ = Γᵈ} Γᵈ' idx (tuple tr)     = recInst (ref-ttr-data-ctx-ext-create-lookup (idx + Data.List.Base.length Γᵈ)) (ref-ttr-helper-tr-helper Γᵈ' (suc idx) tr)
-- ref-ttr-helper {Γᵈ = Γᵈ} Γᵈ' idx (tuple tr)     = recInst (ref-ttr-data-ctx-ext-create-lookup ((ref-ttr-data-ctx Γᵈ) ++ Γᵈ') (idx + Data.List.Base.length Γᵈ)) (ref-ttr-helper-tr-helper Γᵈ' (suc idx) tr)
ref-ttr-helper           Γᵈ' idx (recInst x tr) = recInst (ref-ttr-data-ctx-ext-lookup Γᵈ' x) (ref-ttr-helper-tr-helper Γᵈ' idx tr)

ref-ttr : (e : Γ , Γᵈ ⊢ t) → ((ref-ttr-ctx Γ) , ((ref-ttr-data-ctx Γᵈ) ++ (reverse (ref-ttr-tuple-to-decls e))) ⊢ (ref-ttr-types t))
ref-ttr {Γᵈ = Γᵈ} e = ref-ttr-helper ((reverse (ref-ttr-tuple-to-decls e))) zero e
    