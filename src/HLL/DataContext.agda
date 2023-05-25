{-
    Data context in which data declarations are stored.
    Makes use of De Bruijn indices and discards the name.
 -}
module HLL.DataContext where

open import Agda.Builtin.List

open import HLL.Types

DataCtx : Set
DataCtx = List Decl
