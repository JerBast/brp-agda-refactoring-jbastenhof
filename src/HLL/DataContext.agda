{-
    Data context in which data declarations are stored.
    Makes use of De Bruijn indices and discards the name.
 -}
module HLL.DataContext where

open import Agda.Builtin.List

open import Data.Nat.Base
open import Data.List.Base using (_++_)

open import HLL.Types

open import Utils.Element

DataCtx : Set
DataCtx = List Decl

length : DataCtx → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

-- See: https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
lookup : {Γᵈ : DataCtx} → {n : ℕ} → (p : n < length Γᵈ) → Decl
lookup {(x ∷ _)}  {zero}    (s≤s z≤n) = x
lookup {(_ ∷ xs)} {(suc n)} (s≤s p)   = lookup p

count : ∀ {Γᵈ} → {n : ℕ} → (p : n < length Γᵈ) → lookup p ∈ Γᵈ
count {_ ∷ _}  {zero}    (s≤s z≤n) = here
count {_ ∷ xs} {(suc n)} (s≤s p)   = there (count p)
