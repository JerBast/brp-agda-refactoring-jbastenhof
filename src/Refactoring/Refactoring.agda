{- Refactoring for tuples to records. -}
module Refactoring.Refactoring where

open import Agda.Builtin.List

open import Data.List.Base using (_++_)

open import HLL.HLL
open import HLL.Types
open import HLL.BinOp
open import HLL.Context
open import HLL.DataContext

open import Utils.Element

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        t t'   : Type
        ts ts' : List Type

        op : BinOp

        d : Decl

        Γ Γ'   : Ctx
        Γᵈ Γᵈ' : DataCtx

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Extracts the resolved type list from a type resolver
tr-to-type-list : TypeResolver Γ Γᵈ ts → List Type
tr-to-type-list {ts = ts} _ = ts

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Refactor one type to another
ref-type : Type → Type

-- Refactor all types within a list of types
ref-type-list : List Type → List Type
ref-type-list []       = []
ref-type-list (t ∷ ts) = (ref-type t) ∷ (ref-type-list ts)

ref-type numT        = numT
ref-type charT       = charT
ref-type (t ⇒ u)     = (ref-type t) ⇒ (ref-type u)
ref-type (tupleT ts) = recT (ref-type-list ts)
ref-type (recT ts)   = recT (ref-type-list ts)

-- Refactor a lookup for a type within a type list to a refactored type
-- in a refactored type list
ref-type-list-lookup : t ∈ ts → (ref-type t) ∈ (ref-type-list ts)
ref-type-list-lookup here      = here
ref-type-list-lookup (there x) = there (ref-type-list-lookup x)

-- Refactor all types within the type context
ref-ctx : Ctx → Ctx
ref-ctx = ref-type-list

-- Refactor a lookup for a type within the type context to a refactored
-- type in a refactored context
ref-ctx-lookup : t ∈ Γ → (ref-type t) ∈ (ref-ctx Γ)
ref-ctx-lookup = ref-type-list-lookup

-- Refactor all declarations
ref-decl : Decl → Decl
ref-decl (recDecl ts) = recDecl (ref-type-list ts)

-- Refactor all declarations within a declaration context
ref-d-ctx : DataCtx → DataCtx
ref-d-ctx []       = []
ref-d-ctx (d ∷ ds) = (ref-decl d) ∷ (ref-d-ctx ds)

-- Refactor a lookup for a declaration in a declaration context to a lookup
-- for a refactored declaration in a refactored context
ref-d-ctx-lookup : d ∈ Γᵈ → (ref-decl d) ∈ (ref-d-ctx Γᵈ)
ref-d-ctx-lookup here      = here
ref-d-ctx-lookup (there x) = there (ref-d-ctx-lookup x)

-- Refactor a lookup for a declaration in a declaration context to a lookup
-- for a refactored declaration in an extended refactored context.
-- Note: new declarations are prepended.
ref-d-ctx-ext-lookup : d ∈ Γᵈ → (Γᵈ' : DataCtx) → (ref-decl d) ∈ (ref-d-ctx (Γᵈ' ++ Γᵈ))
ref-d-ctx-ext-lookup x []        = ref-d-ctx-lookup x
ref-d-ctx-ext-lookup x (_ ∷ Γᵈ') = there (ref-d-ctx-ext-lookup x Γᵈ')

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Construct a list of new declarations for all tuples within an expression (postorder traversal)
ref-tuples-to-decls : (e : Γ , Γᵈ ⊢ t) → List Decl

-- Construct a list of new declarations for all tuples within a sequence of expressions
ref-tuples-to-decls-tr : (tr : TypeResolver Γ Γᵈ ts) → List Decl
ref-tuples-to-decls-tr []ᵀ      = []
ref-tuples-to-decls-tr (e ∷ tr) = (ref-tuples-to-decls e) ++ (ref-tuples-to-decls-tr tr)

ref-tuples-to-decls (num n)        = []
ref-tuples-to-decls (char v)       = []
ref-tuples-to-decls (var x)        = []
ref-tuples-to-decls (fun b)        = ref-tuples-to-decls b
ref-tuples-to-decls (f ∙ a)        = (ref-tuples-to-decls f) ++ (ref-tuples-to-decls a)
ref-tuples-to-decls (bin op l r)   = (ref-tuples-to-decls l) ++ (ref-tuples-to-decls r)
ref-tuples-to-decls (tuple tr)     = (recDecl (tr-to-type-list tr)) ∷ (ref-tuples-to-decls-tr tr)
ref-tuples-to-decls (tLookup e x)  = ref-tuples-to-decls e
ref-tuples-to-decls (recInst x tr) = ref-tuples-to-decls-tr tr
ref-tuples-to-decls (rLookup e x)  = ref-tuples-to-decls e

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        Γ₁ Γ₂ : Ctx
        
        t₁ t₂ t₃ : Type
        ts₁ ts₂  : List Type

-- Lookback evidence for the position of an expression within a sequence of expressions
data EmbedIntoTR : TypeResolver Γ Γᵈ ts → TypeResolver Γ Γᵈ ts' → Set where
    tr-root : (tr : TypeResolver Γ Γᵈ ts)
        ---------------------------------
        → EmbedIntoTR tr tr
    
    tr-el : {e : Γ , Γᵈ ⊢ t} {tr₁ : TypeResolver Γ Γᵈ ts₁} {tr₂ : TypeResolver Γ Γᵈ ts₂}
        → EmbedIntoTR (e ∷ tr₁) tr₂
        ---------------------------
        → EmbedIntoTR tr₁ tr₂

-- Lookback evidence for an expression embedded into a larger expression
data EmbedInto : (Γ , Γᵈ ⊢ t) → (Γ₁ , Γᵈ ⊢ t₁) → Set where
    e-root : (e : Γ , Γᵈ ⊢ t)
        ---------------------
        → EmbedInto e e
    
    e-func : {e : Γ , Γᵈ ⊢ t} {e₁ : t₂ ∷ Γ₁ , Γᵈ ⊢ t₁}
        → EmbedInto (fun e₁) e
        ----------------------
        → EmbedInto e₁ e
    
    e-app-l : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₂ , Γᵈ ⊢ t₁} {e₂ : Γ₂ , Γᵈ ⊢ t₁ ⇒ t₂}
        → EmbedInto (e₂ ∙ e₁) e
        -----------------------
        → EmbedInto e₂ e
    
    e-app-r : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₂ , Γᵈ ⊢ t₁} {e₂ : Γ₂ , Γᵈ ⊢ t₁ ⇒ t₂}
        → EmbedInto (e₂ ∙ e₁) e
        -----------------------
        → EmbedInto e₁ e

    e-bin-l : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₂ , Γᵈ ⊢ numT} {e₂ : Γ₂ , Γᵈ ⊢ numT}
        → EmbedInto (bin op e₁ e₂) e
        ----------------------------
        → EmbedInto e₁ e
    
    e-bin-r : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₂ , Γᵈ ⊢ numT} {e₂ : Γ₂ , Γᵈ ⊢ numT}
        → EmbedInto (bin op e₁ e₂) e
        ----------------------------
        → EmbedInto e₂ e
    
    e-tup-e : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts₁}
        → e₁ ∈ᵀ tr
        → EmbedInto (tuple tr) e
        ------------------------
        → EmbedInto e₁ e
    
    e-tup-l : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ tupleT ts} {x : t₁ ∈ ts}
        → EmbedInto (tLookup e₁ x) e
        ----------------------------
        → EmbedInto e₁ e
    
    e-rec-e : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts₁} {x : (recDecl ts₁) ∈ Γᵈ}
        → e₁ ∈ᵀ tr
        → EmbedInto (recInst x tr) e
        ----------------------------
        → EmbedInto e₁ e
    
    e-rec-l : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ recT ts} {x : t₁ ∈ ts}
        → EmbedInto (rLookup e₁ x) e
        ----------------------------
        → EmbedInto e₁ e

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Update declaration lookup after preprending new elements to the declaration context
d-ctx-ext-lookup-l : d ∈ Γᵈ → (Γᵈ' : DataCtx) → d ∈ (Γᵈ' ++ Γᵈ)
d-ctx-ext-lookup-l x []        = x
d-ctx-ext-lookup-l x (_ ∷ Γᵈ') = there (d-ctx-ext-lookup-l x Γᵈ')

-- Update declaration lookup after appending new elements to the declaration context
d-ctx-ext-lookup-r : d ∈ Γᵈ → (Γᵈ' : DataCtx) → d ∈ (Γᵈ ++ Γᵈ')
d-ctx-ext-lookup-r here Γᵈ'      = here
d-ctx-ext-lookup-r (there x) Γᵈ' = there (d-ctx-ext-lookup-r x Γᵈ')

-- Update declaration lookup after appending and prepending new elements to the declaration context
d-ctx-ext-lookup-tr : {e : Γ , Γᵈ ⊢ t} {tr : TypeResolver Γ Γᵈ ts} → e ∈ᵀ tr → d ∈ (ref-tuples-to-decls e) → d ∈ (ref-tuples-to-decls-tr tr)
d-ctx-ext-lookup-tr (here {tr = tr})    ψ = d-ctx-ext-lookup-r ψ (ref-tuples-to-decls-tr tr)
d-ctx-ext-lookup-tr (there {e₂ = e₂} x) ψ = d-ctx-ext-lookup-l (d-ctx-ext-lookup-tr x ψ) (ref-tuples-to-decls e₂)

-- Update declaration lookup in a step-by-step manner. Each step we ascend a level and update the lookup for that level until
-- we reach the root of an expression
ref-t-lookup : {e : Γ , Γᵈ ⊢ t} {e' : Γ' , Γᵈ ⊢ t'} → d ∈ (ref-tuples-to-decls e) → EmbedInto e e' → d ∈ (ref-tuples-to-decls e')
ref-t-lookup x (e-root _)             = x
ref-t-lookup x (e-func ev)            = ref-t-lookup x ev
ref-t-lookup x (e-app-l {e₁ = e₁} ev) = ref-t-lookup (d-ctx-ext-lookup-r x (ref-tuples-to-decls e₁)) ev
ref-t-lookup x (e-app-r {e₂ = e₂} ev) = ref-t-lookup (d-ctx-ext-lookup-l x (ref-tuples-to-decls e₂)) ev
ref-t-lookup x (e-bin-l {e₂ = e₂} ev) = ref-t-lookup (d-ctx-ext-lookup-r x (ref-tuples-to-decls e₂)) ev
ref-t-lookup x (e-bin-r {e₁ = e₁} ev) = ref-t-lookup (d-ctx-ext-lookup-l x (ref-tuples-to-decls e₁)) ev
ref-t-lookup x (e-tup-e ψ ev)         = ref-t-lookup (there (d-ctx-ext-lookup-tr ψ x)) ev
ref-t-lookup x (e-tup-l ev)           = ref-t-lookup x ev
ref-t-lookup x (e-rec-e ψ ev)         = ref-t-lookup (d-ctx-ext-lookup-tr ψ x) ev
ref-t-lookup x (e-rec-l ev)           = ref-t-lookup x ev

-- Update positional lookup in expression sequence from a local point to a centralized point (root of sequence)
ref-tr-lookup : {e : Γ , Γᵈ ⊢ t} {tr₁ : TypeResolver Γ Γᵈ ts₁} {tr₂ : TypeResolver Γ Γᵈ ts₂} → e ∈ᵀ tr₁ → EmbedIntoTR tr₁ tr₂ → e ∈ᵀ tr₂
ref-tr-lookup x (tr-root _) = x
ref-tr-lookup x (tr-el tev) = ref-tr-lookup (there x) tev

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Helper function for refactoring an expression given lookback evidence
ref-h : {e' : Γ' , Γᵈ ⊢ t'} → (e : Γ , Γᵈ ⊢ t) → EmbedInto e e' → ref-ctx Γ , ref-d-ctx ((ref-tuples-to-decls e') ++ Γᵈ) ⊢ ref-type t

-- Helper function for refactoring expressions within a sequence of expressions given lookback and positional evidence (origin: tuple)
ref-tr-tup-h : (tr : TypeResolver Γ Γᵈ ts') → (e' : Γ' , Γᵈ ⊢ t') → EmbedInto (tuple tr) e' → (tr₁ : TypeResolver Γ Γᵈ ts) → EmbedIntoTR tr₁ tr → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
ref-tr-tup-h tr e' ev []ᵀ       tev = []ᵀ
ref-tr-tup-h tr e' ev (e ∷ tr₁) tev = (ref-h e (e-tup-e (ref-tr-lookup here tev) ev)) ∷ (ref-tr-tup-h tr e' ev tr₁ (tr-el tev))

-- Function for refactoring expressions within a sequence of expressions given lookback evidence (origin: tuple)
ref-tr-tup : {e' : Γ' , Γᵈ ⊢ t'} → (tr : TypeResolver Γ Γᵈ ts) → EmbedInto (tuple tr) e' → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
ref-tr-tup {e' = e'} tr ev = ref-tr-tup-h tr e' ev tr (tr-root tr)

-- Helper function for refactoring expressions within a sequence of expressions given lookback and positional evidence (origin: record instance)
ref-tr-rec-h : {x : recDecl ts' ∈ Γᵈ} → (tr : TypeResolver Γ Γᵈ ts') → (e' : Γ' , Γᵈ ⊢ t') → EmbedInto (recInst x tr) e' → (tr₁ : TypeResolver Γ Γᵈ ts) → EmbedIntoTR tr₁ tr → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
ref-tr-rec-h tr e' ev []ᵀ       tev = []ᵀ
ref-tr-rec-h tr e' ev (e ∷ tr₁) tev = (ref-h e (e-rec-e (ref-tr-lookup here tev) ev)) ∷ (ref-tr-rec-h tr e' ev tr₁ (tr-el tev))
 
-- Function for refactoring expressions within a sequence of expressions given lookback evidence (origin: record instance)
ref-tr-rec : {e' : Γ' , Γᵈ ⊢ t'} {x : recDecl ts ∈ Γᵈ} → (tr : TypeResolver Γ Γᵈ ts) → EmbedInto (recInst x tr) e' → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
ref-tr-rec {e' = e'} tr ev = ref-tr-rec-h tr e' ev tr (tr-root tr)

ref-h                     (num n)        ev = num n
ref-h                     (char c)       ev = char c
ref-h                     (var x)        ev = var (ref-ctx-lookup x)
ref-h                     (fun b)        ev = fun (ref-h b (e-func ev))
ref-h                     (f ∙ a)        ev = (ref-h f (e-app-l ev)) ∙ (ref-h a (e-app-r ev))
ref-h                     (bin op l r)   ev = bin op (ref-h l (e-bin-l ev)) (ref-h r (e-bin-r ev))
ref-h {Γᵈ = Γᵈ} {e' = e'} (tuple tr)     ev = recInst (ref-d-ctx-lookup (d-ctx-ext-lookup-r (ref-t-lookup here ev) Γᵈ)) (ref-tr-tup tr ev)
ref-h                     (tLookup e x)  ev = rLookup (ref-h e (e-tup-l ev)) (ref-type-list-lookup x)
ref-h {e' = e'}           (recInst x tr) ev = recInst (ref-d-ctx-ext-lookup x (ref-tuples-to-decls e')) (ref-tr-rec tr ev)
ref-h                     (rLookup e x)  ev = rLookup (ref-h e (e-rec-l ev)) (ref-type-list-lookup x)

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Function for refactoring tuples to records
ref : (e : Γ , Γᵈ ⊢ t) → ref-ctx Γ , ref-d-ctx ((ref-tuples-to-decls e) ++ Γᵈ) ⊢ ref-type t
ref e = ref-h e (e-root e)

-----------------------------------------------------------------------------------------------------------------------------------------------------
      