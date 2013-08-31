module Monad where

open import Applicative

record Monad (F : Set -> Set) : Set₁ where
  field
    return : forall {X} -> X -> F X
    _>>=_ : forall {S T} -> F S -> (S -> F T) -> F T

  applicative : Applicative F
  applicative = record { pure = return;
                         _⊛_ = λ ff fs ->
                                 ff >>= λ f -> fs >>= λ s -> return (f s) }

open Monad {{...}} public
