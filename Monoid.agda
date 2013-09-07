module Monoid where

open import Function using (const)

open import Applicative

record Monoid (X : Set) : Set where
  infixr 4 _∙_
  field
    ε : X
    _∙_ : X -> X -> X

  applicative : Applicative (λ _ -> X)
  applicative = record { pure = const ε;
                         _⊛_ = λ x y → x ∙ y
                       }

open Monoid {{...}} public
