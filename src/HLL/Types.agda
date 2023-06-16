{- Types and declarations for the HLL. -}
module HLL.Types where

open import Agda.Builtin.List

-----------------------------------------------------------------------------------------------------------------------------------------------------

infixr 5 _⇒_

-- Allowed types within the HLL
data Type : Set where
    numT   : Type
    charT  : Type
    _⇒_    : Type → Type → Type
    tupleT : List Type → Type
    recT   : List Type → Type

-- Allowed declarations within the HLL
data Decl : Set where
    recDecl : List Type → Decl

-----------------------------------------------------------------------------------------------------------------------------------------------------
