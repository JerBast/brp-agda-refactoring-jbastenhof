{- Refactoring for tuples to records. -}
module Refactoring.Refactoring where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.List.Base using (_++_)

open import HLL.HLL
open import HLL.Types
open import HLL.Context using (Ctx)
open import HLL.DataContext using (DataCtx)

open import Utils.Element

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        t t'   : Type
        ts ts' : List Type

        d : Decl

        Γ Γ'   : Ctx
        Γᵈ Γᵈ' : DataCtx

-----------------------------------------------------------------------------------------------------------------------------------------------------

{- Extracts the resolved type list from a type resolver. -}

tr-to-type-list : TypeResolver Γ Γᵈ ts → List Type
tr-to-type-list {ts = ts} _ = ts

-----------------------------------------------------------------------------------------------------------------------------------------------------

{- Utility functions for refactoring types in contexts. Replaces tuple types with record types. -}

ref-type : Type → Type

ref-type-list : List Type → List Type
ref-type-list []       = []
ref-type-list (t ∷ ts) = (ref-type t) ∷ (ref-type-list ts)

ref-type numT        = numT
ref-type charT       = charT
ref-type unitT       = unitT
ref-type (t ⇒ u)     = (ref-type t) ⇒ (ref-type u)
ref-type (tupleT ts) = recT (ref-type-list ts)
ref-type (recT ts)   = recT (ref-type-list ts)

ref-ctx : Ctx → Ctx
ref-ctx []      = []
ref-ctx (t ∷ c) = (ref-type t) ∷ (ref-ctx c)

ref-ctx-lookup : t ∈ Γ → (ref-type t) ∈ (ref-ctx Γ)
ref-ctx-lookup here      = here
ref-ctx-lookup (there x) = there (ref-ctx-lookup x)

ref-decl : Decl → Decl
ref-decl (recDecl ts) = recDecl (ref-type-list ts)

ref-d-ctx : DataCtx → DataCtx
ref-d-ctx []       = []
ref-d-ctx (d ∷ ds) = (ref-decl d) ∷ (ref-d-ctx ds)

ref-d-ctx-lookup : d ∈ Γᵈ → (ref-decl d) ∈ (ref-d-ctx Γᵈ)
ref-d-ctx-lookup here      = here
ref-d-ctx-lookup (there x) = there (ref-d-ctx-lookup x)

ref-d-ctx-ext-lookup : d ∈ Γᵈ → (Γᵈ' : DataCtx) → (ref-decl d) ∈ (ref-d-ctx (Γᵈ' ++ Γᵈ))
ref-d-ctx-ext-lookup x []        = ref-d-ctx-lookup x
ref-d-ctx-ext-lookup x (_ ∷ Γᵈ') = there (ref-d-ctx-ext-lookup x Γᵈ')

-----------------------------------------------------------------------------------------------------------------------------------------------------

{- Utility functions for constructing new record declarations from existing tuples. Uses pre-order traversal. -}

ref-tuples-to-decls : (e : Γ , Γᵈ ⊢ t) → List Decl

ref-tuples-to-decls-tr : (tr : TypeResolver Γ Γᵈ ts) → List Decl
ref-tuples-to-decls-tr []ᵀ      = []
ref-tuples-to-decls-tr (e ∷ tr) = (ref-tuples-to-decls e) ++ (ref-tuples-to-decls-tr tr)

ref-tuples-to-decls (num n)        = []
ref-tuples-to-decls (char v)       = []
ref-tuples-to-decls (var x)        = []
ref-tuples-to-decls (fun b)        = ref-tuples-to-decls b
ref-tuples-to-decls (f ∙ a)        = (ref-tuples-to-decls f) ++ (ref-tuples-to-decls a)
ref-tuples-to-decls (tuple tr)     = (recDecl (tr-to-type-list tr)) ∷ (ref-tuples-to-decls-tr tr)
ref-tuples-to-decls (recInst x tr) = ref-tuples-to-decls-tr tr

-----------------------------------------------------------------------------------------------------------------------------------------------------

{- Lookback constructs that allow backwards traversal to the root of an expression. -}

private
    variable
        Γ₁ Γ₂ Γ₃ Γ₄ : Ctx
        
        t₁ t₂ t₃ t₄ : Type
        ts₁ ts₂     : List Type

data EmbedIntoTR : TypeResolver Γ Γᵈ ts → TypeResolver Γ Γᵈ ts' → Set where
    tr-root : (tr : TypeResolver Γ Γᵈ ts)
        ---------------------------------
        → EmbedIntoTR tr tr
    
    tr-el : {e : Γ , Γᵈ ⊢ t} {tr₁ : TypeResolver Γ Γᵈ ts₁} {tr₂ : TypeResolver Γ Γᵈ ts₂}
        → EmbedIntoTR (e ∷ tr₁) tr₂
        ---------------------------
        → EmbedIntoTR tr₁ tr₂

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
    
    e-tup-e : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts₁}
        → e₁ ∈ᵀ tr
        → EmbedInto (tuple tr) e
        ------------------------
        → EmbedInto e₁ e
    
    e-rec-e : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts₁} {x : (recDecl ts₁) ∈ Γᵈ}
        → e₁ ∈ᵀ tr
        → EmbedInto (recInst x tr) e
        ----------------------------
        → EmbedInto e₁ e

-----------------------------------------------------------------------------------------------------------------------------------------------------

{- Functions for extending domains in existing lookups. Support for flat extensions as well as backwards extensions in tree-like expressions. -}

d-ctx-ext-lookup-l : d ∈ Γᵈ → (Γᵈ' : DataCtx) → d ∈ (Γᵈ' ++ Γᵈ)
d-ctx-ext-lookup-l x []        = x
d-ctx-ext-lookup-l x (_ ∷ Γᵈ') = there (d-ctx-ext-lookup-l x Γᵈ')

d-ctx-ext-lookup-r : d ∈ Γᵈ → (Γᵈ' : DataCtx) → d ∈ (Γᵈ ++ Γᵈ')
d-ctx-ext-lookup-r here Γᵈ'      = here
d-ctx-ext-lookup-r (there x) Γᵈ' = there (d-ctx-ext-lookup-r x Γᵈ')

d-ctx-ext-lookup-tr : {e : Γ , Γᵈ ⊢ t} {tr : TypeResolver Γ Γᵈ ts} → e ∈ᵀ tr → d ∈ (ref-tuples-to-decls e) → d ∈ (ref-tuples-to-decls-tr tr)
d-ctx-ext-lookup-tr (here {tr = tr})    ψ = d-ctx-ext-lookup-r ψ (ref-tuples-to-decls-tr tr)
d-ctx-ext-lookup-tr (there {e₂ = e₂} x) ψ = d-ctx-ext-lookup-l (d-ctx-ext-lookup-tr x ψ) (ref-tuples-to-decls e₂)

ref-t-lookup : {e : Γ , Γᵈ ⊢ t} {e' : Γ' , Γᵈ ⊢ t'} → d ∈ (ref-tuples-to-decls e) → EmbedInto e e' → d ∈ (ref-tuples-to-decls e')
ref-t-lookup x (e-root _)             = x
ref-t-lookup x (e-func ev)            = ref-t-lookup x ev
ref-t-lookup x (e-app-l {e₁ = e₁} ev) = ref-t-lookup (d-ctx-ext-lookup-r x (ref-tuples-to-decls e₁)) ev
ref-t-lookup x (e-app-r {e₂ = e₂} ev) = ref-t-lookup (d-ctx-ext-lookup-l x (ref-tuples-to-decls e₂)) ev
ref-t-lookup x (e-tup-e ψ ev)         = ref-t-lookup (there (d-ctx-ext-lookup-tr ψ x)) ev
ref-t-lookup x (e-rec-e ψ ev)         = ref-t-lookup (d-ctx-ext-lookup-tr ψ x) ev

ref-tr-lookup : {e : Γ , Γᵈ ⊢ t} {tr₁ : TypeResolver Γ Γᵈ ts₁} {tr₂ : TypeResolver Γ Γᵈ ts₂} → e ∈ᵀ tr₁ → EmbedIntoTR tr₁ tr₂ → e ∈ᵀ tr₂
ref-tr-lookup x (tr-root _) = x
ref-tr-lookup x (tr-el tev) = ref-tr-lookup (there x) tev

-----------------------------------------------------------------------------------------------------------------------------------------------------

{- Helper functions for refactoring expressions using lookback evidence. -}

ref-h : {e' : Γ' , Γᵈ ⊢ t'} → (e : Γ , Γᵈ ⊢ t) → EmbedInto e e' → ref-ctx Γ , ref-d-ctx ((ref-tuples-to-decls e') ++ Γᵈ) ⊢ ref-type t

ref-tr-tup : {e' : Γ' , Γᵈ ⊢ t'} → (tr : TypeResolver Γ Γᵈ ts) → EmbedInto (tuple tr) e' → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
ref-tr-tup {Γᵈ = Γᵈ} {Γ = Γ} {e' = e'} tr ev = ref-tr-tup-h tr (tr-root tr)
    where
        ref-tr-tup-h : (tr₁ : TypeResolver Γ Γᵈ ts) → EmbedIntoTR tr₁ tr → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
        ref-tr-tup-h []ᵀ      tev = []ᵀ
        ref-tr-tup-h (e ∷ tr) tev = (ref-h e (e-tup-e (ref-tr-lookup here tev) ev)) ∷ (ref-tr-tup-h tr (tr-el tev))

ref-tr-rec : {e' : Γ' , Γᵈ ⊢ t'} {x : recDecl ts ∈ Γᵈ} → (tr : TypeResolver Γ Γᵈ ts) → EmbedInto (recInst x tr) e' → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
ref-tr-rec {Γᵈ = Γᵈ} {Γ = Γ} {e' = e'} tr ev = ref-tr-rec-h tr (tr-root tr)
    where
        ref-tr-rec-h : (tr₁ : TypeResolver Γ Γᵈ ts) → EmbedIntoTR tr₁ tr → TypeResolver (ref-ctx Γ) (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-type-list ts)
        ref-tr-rec-h []ᵀ      tev = []ᵀ
        ref-tr-rec-h (e ∷ tr) tev = (ref-h e (e-rec-e (ref-tr-lookup here tev) ev)) ∷ (ref-tr-rec-h tr (tr-el tev))

ref-h                     (num n)        ev = num n
ref-h                     (char c)       ev = char c
ref-h                     (var x)        ev = var (ref-ctx-lookup x)
ref-h                     (fun b)        ev = fun (ref-h b (e-func ev))
ref-h                     (f ∙ a)        ev = (ref-h f (e-app-l ev)) ∙ (ref-h a (e-app-r ev))
ref-h {Γᵈ = Γᵈ} {e' = e'} (tuple tr)     ev = recInst (ref-d-ctx-lookup (d-ctx-ext-lookup-r (ref-t-lookup here ev) Γᵈ)) (ref-tr-tup tr ev)
ref-h {e' = e'}           (recInst x tr) ev = recInst (ref-d-ctx-ext-lookup x (ref-tuples-to-decls e')) (ref-tr-rec tr ev)

-----------------------------------------------------------------------------------------------------------------------------------------------------

{- The core refactoring operation that replaces tuples with records for arbitrary expressions. -}

ref : (e : Γ , Γᵈ ⊢ t) → ref-ctx Γ , ref-d-ctx ((ref-tuples-to-decls e) ++ Γᵈ) ⊢ ref-type t
ref e = ref-h e (e-root e)

-----------------------------------------------------------------------------------------------------------------------------------------------------
      