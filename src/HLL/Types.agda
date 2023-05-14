{-
    Types for the HLL.
 -}
module HLL.Types where

open import Agda.Builtin.List

infixr 5 _⇒_

data Type : Set where
    numT   : Type
    charT  : Type
    _⇒_    : Type → Type → Type
    tupleT : List Type → Type
