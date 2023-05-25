module Utils.Element where

open import Agda.Builtin.List

private
    variable
        A : Set
        as : List A
        a a₁ a₂ : A

data _∈_ : A → List A → Set where
    here  : a ∈ (a ∷ as)
    there : a₁ ∈ as → a₁ ∈ (a₂ ∷ as)
