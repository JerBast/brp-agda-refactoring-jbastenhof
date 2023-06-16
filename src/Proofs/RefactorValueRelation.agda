{- Value relationship between the big-step semantics of an expression and its refactored counterpart. -}
module Proofs.RefactorValueRelation where

open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

open import Data.Product
open import Data.List.Base using (_++_)

open import HLL.HLL
open import HLL.Types
open import HLL.Values
open import HLL.Context
open import HLL.DataContext
open import HLL.DynamicSemantics

open import Refactoring.Refactoring

open import Utils.Element

-----------------------------------------------------------------------------------------------------------------------------------------------------

private
    variable
        t t'   : Type
        ts ts' : List Type

        v : Value t

        d : Decl

        Γ Γ'   : Ctx
        Γᵈ Γᵈ' : DataCtx

        t₁ t₂ t₃ : Type
        v₁ : Value t₁
        v₂ : Value t₂
        v₃ : Value t₃

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Relation from one value to another
_⟶ⱽ_ : Value t → Value (ref-type t) → Set

-- Sequence of relations from one value to another
_⟶ᴾⱽ_ : PolyList ts → PolyList (ref-type-list ts) → Set
[]         ⟶ᴾⱽ []         = ⊤
(v₁ ∷ vs₁) ⟶ᴾⱽ (v₂ ∷ vs₂) = (v₁ ⟶ⱽ v₂) × (vs₁ ⟶ᴾⱽ vs₂)

num n₁                          ⟶ⱽ num n₂                       = n₁ ≡ n₂
char c₁                         ⟶ⱽ char c₂                      = c₁ ≡ c₂
clos {t} {_} {Γᵈ} {u = u} b₁ γ₁ ⟶ⱽ clos {_} {_} {Γᵈ₁} {_} b₂ γ₂ = {vᵀ₁ : Value t} {vᵁ₁ : Value u} {vᵀ₂ : Value (ref-type t)} {vᵁ₂ : Value (ref-type u)} {vᵀ₁⟶vᵀ₂ : vᵀ₁ ⟶ⱽ vᵀ₂}
    → (vᵀ₁ ∷ γ₁) , Γᵈ  ⊢ b₁ ⇓ vᵁ₁
    → (vᵀ₂ ∷ γ₂) , Γᵈ₁ ⊢ b₂ ⇓ vᵁ₂
    → vᵁ₁ ⟶ⱽ vᵁ₂
tuple vs₁                       ⟶ⱽ rec vs₂                      = vs₁ ⟶ᴾⱽ vs₂
rec vs₁                         ⟶ⱽ rec vs₂                      = vs₁ ⟶ᴾⱽ vs₂

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Relation between all values of an environment pre- and post-refactoring
_⟶ᴱ_ : Env Γ → Env (ref-ctx Γ) → Set
_⟶ᴱ_ = _⟶ᴾⱽ_

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Proof for relating a value within an environment to its counterpart in a refactored environment
ref-lookup-v : {x : t ∈ Γ} {γ₁ : Env Γ} {γ₂ : Env (ref-ctx Γ)} → (γ₁ ⟶ᴱ γ₂) → value-lookup γ₁ x ⟶ⱽ value-lookup γ₂ (ref-ctx-lookup x)
ref-lookup-v {x = here}    {γ₁ = v₁ ∷ γ₁} {v₂ ∷ γ₂} r = proj₁ r
ref-lookup-v {x = there x} {γ₁ = v₁ ∷ γ₁} {v₂ ∷ γ₂} r = ref-lookup-v (proj₂ r)

-- Proof for relating a value in a sequence to its counterpart in a sequence of refactored expressions
ref-lookup-pl : {x : t ∈ ts} {pl₁ : PolyList ts} {pl₂ : PolyList (ref-type-list ts)} → pl₁ ⟶ᴾⱽ pl₂ → poly-list-lookup pl₁ x ⟶ⱽ poly-list-lookup pl₂ (ref-type-list-lookup x)
ref-lookup-pl {x = here}    {v₁ ∷ pl₁} {v₂ ∷ pl₂} r = proj₁ r
ref-lookup-pl {x = there x} {v₁ ∷ pl₁} {v₂ ∷ pl₂} r = ref-lookup-pl (proj₂ r)

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Helper function for constructing the value relation based on a pre- and post-refactor expression
proof-h : {γ₁ : Env Γ} {γ₂ : Env (ref-ctx Γ)} {e : Γ , Γᵈ ⊢ t} {e' : Γ' , Γᵈ ⊢ t'}
    → (ev : EmbedInto e e')
    → γ₁ , Γᵈ                                       ⊢ e          ⇓ v₁
    → γ₂ , ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ) ⊢ ref-h e ev ⇓ v₂
    → γ₁ ⟶ᴱ γ₂
    → v₁ ⟶ⱽ v₂

proof-h-rr-tup : {γ₁ : Env Γ} {γ₂ : Env (ref-ctx Γ)} {e' : Γ' , Γᵈ ⊢ t'} {tr₁ : TypeResolver Γ Γᵈ ts} {pl₁ : PolyList ts} {pl₂ : PolyList (ref-type-list ts)}
    → (ev : EmbedInto (tuple tr₁) e')
    → ReductionResolver γ₁ Γᵈ tr₁ pl₁
    → ReductionResolver γ₂ (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-tr-tup tr₁ ev) pl₂
    → γ₁ ⟶ᴱ γ₂
    → tuple pl₁ ⟶ⱽ rec pl₂
proof-h-rr-tup {Γ} {Γᵈ = Γᵈ} {e' = e'} {tr₁ = tr₁} ev rr₁ rr₂ γ = proof-h-rr-tup-h (tr-root tr₁) rr₁ rr₂ γ
    where
        proof-h-rr-tup-h : {γ₁ : Env Γ} {γ₂ : Env (ref-ctx Γ)} {tr₁' : TypeResolver Γ Γᵈ ts} {pl₁ : PolyList ts} {pl₂ : PolyList (ref-type-list ts)} → (tev : EmbedIntoTR tr₁' tr₁) → ReductionResolver γ₁ Γᵈ tr₁' pl₁ → ReductionResolver γ₂ (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-tr-tup-h tr₁ e' ev tr₁' tev) pl₂ → γ₁ ⟶ᴱ γ₂ → pl₁ ⟶ᴾⱽ pl₂
        proof-h-rr-tup-h tev []ᴿ        []ᴿ        γ = tt
        proof-h-rr-tup-h tev (e₁ ∷ rr₁) (e₂ ∷ rr₂) γ = proof-h (e-tup-e (ref-tr-lookup here tev) ev) e₁ e₂ γ , proof-h-rr-tup-h (tr-el tev) rr₁ rr₂ γ

proof-h-rr-rec : {γ₁ : Env Γ} {γ₂ : Env (ref-ctx Γ)} {x : recDecl ts ∈ Γᵈ} {e' : Γ' , Γᵈ ⊢ t'} {tr₁ : TypeResolver Γ Γᵈ ts} {pl₁ : PolyList ts} {pl₂ : PolyList (ref-type-list ts)}
    → (ev : EmbedInto (recInst x tr₁) e')
    → ReductionResolver γ₁ Γᵈ tr₁ pl₁
    → ReductionResolver γ₂ (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-tr-rec tr₁ ev) pl₂
    → γ₁ ⟶ᴱ γ₂
    → tuple pl₁ ⟶ⱽ rec pl₂
proof-h-rr-rec {Γ} {Γᵈ = Γᵈ} {e' = e'} {tr₁ = tr₁} ev rr₁ rr₂ γ = proof-h-rr-tup-h (tr-root tr₁) rr₁ rr₂ γ
    where
        proof-h-rr-tup-h : {γ₁ : Env Γ} {γ₂ : Env (ref-ctx Γ)} {tr₁' : TypeResolver Γ Γᵈ ts} {pl₁ : PolyList ts} {pl₂ : PolyList (ref-type-list ts)} → (tev : EmbedIntoTR tr₁' tr₁) → ReductionResolver γ₁ Γᵈ tr₁' pl₁ → ReductionResolver γ₂ (ref-d-ctx (ref-tuples-to-decls e' ++ Γᵈ)) (ref-tr-rec-h tr₁ e' ev tr₁' tev) pl₂ → γ₁ ⟶ᴱ γ₂ → pl₁ ⟶ᴾⱽ pl₂
        proof-h-rr-tup-h tev []ᴿ        []ᴿ        γ = tt
        proof-h-rr-tup-h tev (e₁ ∷ rr₁) (e₂ ∷ rr₂) γ = proof-h (e-rec-e (ref-tr-lookup here tev) ev) e₁ e₂ γ , proof-h-rr-tup-h (tr-el tev) rr₁ rr₂ γ

proof-h ev ⇓num            ⇓num            _                             = refl
proof-h ev ⇓char           ⇓char           _                             = refl
proof-h ev ⇓var            ⇓var            γ                             = ref-lookup-v γ
proof-h ev ⇓fun ⇓fun                       γ {vᵀ₁⟶vᵀ₂ = vᵀ₁⟶vᵀ₂} e₁ e₂ = proof-h (e-func ev) e₁ e₂ (vᵀ₁⟶vᵀ₂ , γ)
proof-h ev (⇓app f₁ b₁ a₁) (⇓app f₂ b₂ a₂) γ                             = (proof-h (e-app-l ev) f₁ f₂ γ) {vᵀ₁⟶vᵀ₂ = proof-h (e-app-r ev) a₁ a₂ γ} b₁ b₂
proof-h ev (⇓tuple rr₁)    (⇓recInst rr₂)  γ                             = proof-h-rr-tup ev rr₁ rr₂ γ
proof-h ev (⇓tLookup e₁)   (⇓rLookup e₂)   γ                             = ref-lookup-pl (proof-h (e-tup-l ev) e₁ e₂ γ)
proof-h ev (⇓recInst rr₁)  (⇓recInst rr₂)  γ                             = proof-h-rr-rec ev rr₁ rr₂ γ
proof-h ev (⇓rLookup e₁)   (⇓rLookup e₂)   γ                             = ref-lookup-pl (proof-h (e-rec-l ev) e₁ e₂ γ)

-----------------------------------------------------------------------------------------------------------------------------------------------------

-- Function for constructing the value relation based on a pre- and post-refactor expression
proof : {e : [] , Γᵈ ⊢ t} → [] , Γᵈ ⊢ e ⇓ v₁ → [] , ref-d-ctx (ref-tuples-to-decls e ++ Γᵈ) ⊢ ref e ⇓ v₂ → v₁ ⟶ⱽ v₂
proof {e = e} e₁ e₂ = proof-h (e-root e) e₁ e₂ tt

-----------------------------------------------------------------------------------------------------------------------------------------------------

ex₁-e : [] , [] ⊢ numT
ex₁-e = num 42

ex₁-v₁ : [] , [] ⊢ ex₁-e ⇓ num 42
ex₁-v₁ = ⇓num

ex₁-v₂ : [] , [] ⊢ ref ex₁-e ⇓ num 42
ex₁-v₂ = ⇓num

ex₁ : num 42 ⟶ⱽ num 42
ex₁ = proof ex₁-v₁ ex₁-v₂

-----------------------------------------------------------------------------------------------------------------------------------------------------

ex₂-e : [] , [] ⊢ tupleT (numT ∷ charT ∷ [])
ex₂-e = tuple (num 42 ∷ char 'J' ∷ []ᵀ)

ex₂-v₁ : [] , [] ⊢ ex₂-e ⇓ tuple (num 42 ∷ char 'J' ∷ [])
ex₂-v₁ = ⇓tuple (⇓num ∷ ⇓char ∷ []ᴿ)

ex₂-v₂ : [] , recDecl (numT ∷ charT ∷ []) ∷ [] ⊢ ref ex₂-e ⇓ rec (num 42 ∷ char 'J' ∷ [])
ex₂-v₂ = ⇓recInst (⇓num ∷ ⇓char ∷ []ᴿ)

ex₂ : tuple (num 42 ∷ char 'J' ∷ []) ⟶ⱽ rec (num 42 ∷ char 'J' ∷ [])
ex₂ = proof ex₂-v₁ ex₂-v₂

-----------------------------------------------------------------------------------------------------------------------------------------------------
