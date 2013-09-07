module Traversable where

open import EndoFunctor
open import Applicative using (Applicative; applicativeId)

record Traversable (F : Set -> Set) : Set₁ where
  field
    traverse : forall {G S T} {{AG : Applicative G}} ->
               (S -> G T) -> F S -> G (F T)

  endofunctor : EndoFunctor F
  endofunctor = record { map = traverse }

open Traversable {{...}} public
