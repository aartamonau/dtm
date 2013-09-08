module Traversable where

open import Function using (id; _∘_)

open import EndoFunctor
open import Applicative using (Applicative; applicativeId; pure; _⊛_)
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

traversableId : Traversable id
traversableId = record {traverse = id}

traversableComp : forall {F G} -> Traversable F -> Traversable G ->
                  Traversable (F ∘ G)
traversableComp {F} {G} f g = record { traverse = tr }
  where tr : forall {A S T} {{_ : Applicative A}} ->
             (S -> A T) -> F (G S) -> A (F (G T))
        tr = traverse {{f}} ∘ traverse {{g}}
