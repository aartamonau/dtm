module Applicative where

open import EndoFunctor

record Applicative (F : Set -> Set) : Set₁ where
  field
    pure : forall {X} -> X -> F X
    _⊛_ : forall {S T} -> F (S -> T) -> F S -> F T

  endofunctor : EndoFunctor F
  endofunctor = record { map = λ f x -> pure f ⊛ x }

open Applicative {{...}} public
