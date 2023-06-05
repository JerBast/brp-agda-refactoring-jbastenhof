module Utils.Element where

open import Data.Fin.Base
open import Data.List.Base

private
    variable
        A : Set
        as : List A
        a a₁ a₂ : A

data _∈_ : A → List A → Set where
    here  : a ∈ (a ∷ as)
    there : a₁ ∈ as → a₁ ∈ (a₂ ∷ as)

index : a ∈ as → Fin (length as)
index here      = zero
index (there x) = suc (index x)
