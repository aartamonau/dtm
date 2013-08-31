module EndoFunctor where

record EndoFunctor (F : Set -> Set) : Set₁ where
  field
    map : forall {S T} -> (S -> T) -> F S -> F T

open EndoFunctor {{...}} public
