module Vec where

open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Fin

open import Function using (_∘_)

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

zip : forall {n S T} -> Vec S n -> Vec T n -> Vec (S × T) n
zip ss ts = vapp (vmap _,_ ss) ts

proj : forall {n X} -> Vec X n -> Fin n -> X
proj (x , xs) zero = x
proj (x , xs) (suc i) = proj xs i

tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {zero} f = ⟨⟩
tabulate {suc n} f = f zero , tabulate (f ∘ suc)
