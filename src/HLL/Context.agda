{-
    Context in which the types are stored.
    Makes use of De Bruijn indices and discards the name.
 -}
module HLL.Context where

open import Agda.Builtin.List

open import Data.Nat.Base
open import Data.List.Base using (_++_)

open import HLL.Types

open import Utils.Element

Ctx : Set
Ctx = List Type

length : Ctx → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

-- See: https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
lookup : {Γ : Ctx} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(x ∷ _)}  {zero}    (s≤s z≤n) = x
lookup {(_ ∷ xs)} {(suc n)} (s≤s p)   = lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → lookup p ∈ Γ
count {_ ∷ _}  {zero}    (s≤s z≤n) = here
count {_ ∷ xs} {(suc n)} (s≤s p)   = there (count p)
