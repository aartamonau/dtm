module Traversable where

open import EndoFunctor
open import Applicative using (Applicative; applicativeId)
open import Monoid using (Monoid; applicative)

record Traversable (F : Set -> Set) : Set₁ where
  field
    traverse : forall {G S T} {{AG : Applicative G}} ->
               (S -> G T) -> F S -> G (F T)

  endofunctor : EndoFunctor F
  endofunctor = record { map = traverse }

open Traversable {{...}} public

data One : Set where

crush : forall {F X Y} {{TF : Traversable F}} {{M : Monoid Y}} ->
        (X -> Y) -> F X -> Y
crush {{ M = M }} = traverse {T = One} {{ AG = applicative {{ M }} }}
