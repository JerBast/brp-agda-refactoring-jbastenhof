{- Refactoring for tuples to records. -}
module Refactoring.Refactoring where

open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Data.List.Base using (_++_; _∷ʳ_)

open import HLL.HLL
open import HLL.Types
open import HLL.Context hiding (length)
open import HLL.DataContext

open import Utils.Element

private
    variable
        t t'   : Type
        ts ts' : List Type

        d : Decl

        Γ Γ'   : Ctx
        Γᵈ Γᵈ' : DataCtx

-----------------------------------------------------------------------------------------------------------------------------------------------------

tr-to-type-list : TypeResolver Γ Γᵈ ts → List Type
tr-to-type-list {ts = ts} _ = ts

-----------------------------------------------------------------------------------------------------------------------------------------------------

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

_++ᵀ_ : TypeResolver Γ Γᵈ ts → TypeResolver Γ Γᵈ ts' → TypeResolver Γ Γᵈ (ts ++ ts')
[]ᵀ       ++ᵀ tr₂ = tr₂
(e ∷ tr₁) ++ᵀ tr₂ = e ∷ (tr₁ ++ᵀ tr₂)

_∷ᵀʳ_ : TypeResolver Γ Γᵈ ts → (Γ , Γᵈ ⊢ t) → TypeResolver Γ Γᵈ (ts ∷ʳ t)
tr ∷ᵀʳ e = tr ++ᵀ (e ∷ []ᵀ) 

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        Γ₁ Γ₂ Γ₃ Γ₄ : Ctx
        
        t₁ t₂ t₃ t₄ : Type
        ts₁ ts₂     : List Type

data EmbedInto : (Γ , Γᵈ ⊢ t) → (Γ₁ , Γᵈ ⊢ t₁) → Set where
    e-root : (e : Γ , Γᵈ ⊢ t) → EmbedInto e e
    
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
    
    -- e-func : {e : Γ , Γᵈ ⊢ t} {e₁ : t₂ ∷ Γ₁ , Γᵈ ⊢ t₁}
    --     → EmbedInto e e₁
    --     ----------------------
    --     → EmbedInto e (fun e₁)
    
    -- e-app-l : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₂ , Γᵈ ⊢ t₁} {e₂ : Γ₂ , Γᵈ ⊢ t₁ ⇒ t₂}
    --     → EmbedInto (e₂ ∙ e₁) e
    --     → EmbedInto e₂ (e₂ ∙ e₁)
    
    -- e-app-r : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₂ , Γᵈ ⊢ t₁} {e₂ : Γ₂ , Γᵈ ⊢ t₁ ⇒ t₂}
    --     → EmbedInto (e₂ ∙ e₁) e
    --     → EmbedInto e₁ (e₂ ∙ e₁)
    
    -- e-tup-e : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁}
    --     → (tr₁ : TypeResolver Γ₁ Γᵈ ts)
    --     → (tr₂ : TypeResolver Γ₁ Γᵈ ts')
    --     → EmbedInto (tuple (tr₁ ++ᵀ (e₁ ∷ tr₂))) e
    --     → EmbedInto e₁ (tuple (tr₁ ++ᵀ (e₁ ∷ tr₂)))
    
    -- e-tup-e : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts}
    --     → EmbedInto (tuple (e₁ ∷ tr)) e
    --     → EmbedInto e₁ (tuple (e₁ ∷ tr))
    
    -- e-tup-tr : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts}
    --     → EmbedInto (tuple (e₁ ∷ tr)) e
    --     → EmbedInto (tuple tr) (tuple (e₁ ∷ tr))
    
    -- e-rec-e : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts}
    --     → EmbedInto (recInst {!   !} (e₁ ∷ tr)) e
    --     → EmbedInto e₁ (recInst {!   !} (e₁ ∷ tr))
    
    -- e-rec-tr : {e : Γ , Γᵈ ⊢ t} {e₁ : Γ₁ , Γᵈ ⊢ t₁} {tr : TypeResolver Γ₁ Γᵈ ts} {x : recDecl (t₁ ∷ ts) ∈ Γᵈ}
    --     → EmbedInto (recInst x (e₁ ∷ tr)) e
    --     → EmbedInto (recInst {! x  !} tr) (recInst {!   !} (e₁ ∷ tr))

-----------------------------------------------------------------------------------------------------------------------------------------------------

d-ctx-ext-lookup-l : d ∈ Γᵈ → (Γᵈ' : DataCtx) → d ∈ (Γᵈ' ++ Γᵈ)
d-ctx-ext-lookup-l x []        = x
d-ctx-ext-lookup-l x (_ ∷ Γᵈ') = there (d-ctx-ext-lookup-l x Γᵈ')

d-ctx-ext-lookup-r : d ∈ Γᵈ → (Γᵈ' : DataCtx) → d ∈ (Γᵈ ++ Γᵈ')
d-ctx-ext-lookup-r here Γᵈ'      = here
d-ctx-ext-lookup-r (there x) Γᵈ' = there (d-ctx-ext-lookup-r x Γᵈ')

ref-t-lookup : {e : Γ , Γᵈ ⊢ t} {e' : Γ' , Γᵈ ⊢ t'} → d ∈ (ref-tuples-to-decls e) → EmbedInto e e' → d ∈ (ref-tuples-to-decls e')
ref-t-lookup x (e-root _)             = x
ref-t-lookup x (e-func ev)            = ref-t-lookup x ev
ref-t-lookup x (e-app-l {e₁ = e₁} ev) = ref-t-lookup (d-ctx-ext-lookup-r x (ref-tuples-to-decls e₁)) ev
ref-t-lookup x (e-app-r {e₂ = e₂} ev) = ref-t-lookup (d-ctx-ext-lookup-l x (ref-tuples-to-decls e₂)) ev

-----------------------------------------------------------------------------------------------------------------------------------------------------

ref-h : {e' : Γ' , Γᵈ ⊢ t'} → (e : Γ , Γᵈ ⊢ t) → EmbedInto e e' → ref-ctx Γ , ref-d-ctx ((ref-tuples-to-decls e') ++ Γᵈ) ⊢ ref-type t
ref-h                     (num n)        ev = num n
ref-h                     (char c)       ev = char c
ref-h                     (var x)        ev = var (ref-ctx-lookup x)
ref-h                     (fun b)        ev = fun (ref-h b (e-func ev))
ref-h                     (f ∙ a)        ev = (ref-h f (e-app-l ev)) ∙ (ref-h a (e-app-r ev))
ref-h {Γᵈ = Γᵈ} {e' = e'} (tuple tr)     ev = recInst (ref-d-ctx-lookup (d-ctx-ext-lookup-r (ref-t-lookup here ev) Γᵈ)) {!   !}
ref-h {e' = e'}           (recInst x tr) ev = recInst (ref-d-ctx-ext-lookup x (ref-tuples-to-decls e')) {!   !}

-----------------------------------------------------------------------------------------------------------------------------------------------------

ref : (e : Γ , Γᵈ ⊢ t) → ref-ctx Γ , ref-d-ctx ((ref-tuples-to-decls e) ++ Γᵈ) ⊢ ref-type t
ref e = ref-h e (e-root e)

-----------------------------------------------------------------------------------------------------------------------------------------------------
 