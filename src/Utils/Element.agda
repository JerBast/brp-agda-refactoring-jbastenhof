{- Utility module for stating that some value is an element of a list. -}
module Utils.Element where

open import Data.List.Base

private
    variable
        A : Set
        as : List A
        a a₁ a₂ : A

data _∈_ : A → List A → Set where
    here  : a ∈ (a ∷ as)
    there : a₁ ∈ as → a₁ ∈ (a₂ ∷ as)
