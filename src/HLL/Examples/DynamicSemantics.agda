{- Examples/test programs for the dynamic semantics. -}
module HLL.Examples.DynamicSemantics where

open import Agda.Builtin.List

open import HLL.HLL
open import HLL.Types
open import HLL.Values
open import HLL.Context
open import HLL.DataContext
open import HLL.DynamicSemantics

open import Utils.Element

-- Examples
ex1 : [] , [] ⊢ num 42 ⇓ num 42
ex1 = ⇓num

ex2 : [] , [] ⊢ (fun (var here)) ∙ (num 42) ⇓ num 42
ex2 = ⇓app ⇓fun ⇓var ⇓num

ex3 : [] , [] ⊢ tuple (char 'Z' ∷ num 10 ∷ []ᵀ) ⇓ tuple (char 'Z' ∷ num 10 ∷ [])
ex3 = ⇓tuple (⇓char ∷ ⇓num ∷ []ᴿ)

ex4 : [] , recDecl (charT ∷ numT ∷ numT ∷ []) ∷ [] ⊢ recInst here (char 'Z' ∷ num 42 ∷ num 1337 ∷ []ᵀ) ⇓ rec (char 'Z' ∷ num 42 ∷ num 1337 ∷ [])
ex4 = ⇓recInst (⇓char ∷ ⇓num ∷ ⇓num ∷ []ᴿ)

ex5 : [] , [] ⊢ tLookup (tuple (char 'Z' ∷ num 10 ∷ []ᵀ)) (there here) ⇓ num 10
ex5 = ⇓tLookup (⇓tuple (⇓char ∷ ⇓num ∷ []ᴿ))

ex6 : [] , [] ⊢ tLookup (tuple (char 'Z' ∷ num 10 ∷ num 10 ∷ []ᵀ)) (there (there here)) ⇓ num 10
ex6 = ⇓tLookup (⇓tuple (⇓char ∷ ⇓num ∷ ⇓num ∷ []ᴿ))

ex7 : [] , recDecl (charT ∷ numT ∷ numT ∷ []) ∷ [] ⊢ rLookup (recInst here (char 'Z' ∷ num 10 ∷ num 10 ∷ []ᵀ)) (there (there here)) ⇓ num 10
ex7 = ⇓rLookup (⇓recInst (⇓char ∷ ⇓num ∷ ⇓num ∷ []ᴿ))
