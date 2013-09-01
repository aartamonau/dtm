module Vec where

open import Applicative as App hiding (endofunctor)

open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Fin

open import EndoFunctor

open import Function using (_∘_)

open import Monad hiding (applicative)

data Vec (X : Set) : ℕ -> Set where
  ⟨⟩ : Vec X 0
  _,_ : {n : ℕ} -> X -> Vec X n -> Vec X (suc n)

infixr 4 _,_

vec : forall {n X} -> X -> Vec X n
vec {zero} x = ⟨⟩
vec {suc n} x = x , vec x

vapp : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp ⟨⟩ ⟨⟩ = ⟨⟩
vapp (f , fs) (s , ss) = f s , vapp fs ss

vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap f ss = vapp (vec f) ss

vhead : forall {n X} -> Vec X (suc n) -> X
vhead (x , xs) = x

vtail : forall {n X} -> Vec X (suc n) -> Vec X n
vtail (x , xs) = xs

zip : forall {n S T} -> Vec S n -> Vec T n -> Vec (S × T) n
zip ss ts = vapp (vmap _,_ ss) ts

proj : forall {n X} -> Vec X n -> Fin n -> X
proj (x , xs) zero = x
proj (x , xs) (suc i) = proj xs i

tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {zero} f = ⟨⟩
tabulate {suc n} f = f zero , tabulate (f ∘ suc)

applicative : forall {n} -> Applicative (λ X -> Vec X n)
applicative = record { pure = vec; _⊛_ = vapp }

endofunctor : forall {n} -> EndoFunctor (λ X -> Vec X n)
endofunctor = App.endofunctor

-- https://github.com/jvranish/FixedList/blob/master/src/Data/FixedList.hs#L27
monad : forall {n} -> Monad (λ X -> Vec X n)
monad = record { return = vec;
                 _>>=_ = bind }
      where bind : forall {n S T} -> Vec S n -> (S -> Vec T n) -> Vec T n
            bind ⟨⟩ k = ⟨⟩
            bind (x , xs) k = vhead (k x) , bind xs (vtail ∘ k)
