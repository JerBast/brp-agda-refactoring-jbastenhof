{-
    Context in which the types are stored.
    Makes use of De Bruijn indices and discards the names.
 -}
module HLL.Context where

open import Agda.Builtin.List

open import HLL.Types

Ctx : Set
Ctx = List Type
