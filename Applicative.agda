module Applicative where

open import Function using (id; _∘_)

open import EndoFunctor

record Applicative (F : Set -> Set) : Set₁ where
  field
    pure : forall {X} -> X -> F X
    _⊛_ : forall {S T} -> F (S -> T) -> F S -> F T

  endofunctor : EndoFunctor F
  endofunctor = record { map = λ f x -> pure f ⊛ x }

open Applicative {{...}} public

applicativeId : Applicative id
applicativeId = record { pure = id; _⊛_ = id }

applicativeComp : forall {F G} -> Applicative F -> Applicative G -> Applicative (F ∘ G)
applicativeComp {F} {G} f g =
  record { pure = λ x → pure {{f}} (pure {{g}} x);
           _⊛_ = λ k x -> (pure {{f}} (_⊛_ {{g}}) fapp k) fapp x
         }
  where _fapp_ : forall {S T} -> F (S -> T) -> F S -> F T
        _fapp_ = _⊛_ {{f}}

data Product (F G : Set -> Set) (X : Set) : Set where
  prod : F X -> G X -> Product F G X

applicativePointwiseProduct : forall {F G} -> Applicative F -> Applicative G
                                           -> Applicative (Product F G)
applicativePointwiseProduct {F} {G} f g = record { pure = λ x -> prod (pure x) (pure x);
                                                   _⊛_ = appProduct
                                                 }
 where appProduct : forall {S T} -> Product F G (S -> T) -> Product F G S -> Product F G T
       appProduct (prod f g) (prod x y) = prod (f ⊛ x) (g ⊛ y)
