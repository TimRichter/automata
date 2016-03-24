module FinSupp

-- supplementary stuff on Fin

%default total

import Control.Isomorphism
import Injective

-- miss x is the increasing function Fin n -> Fin (S n) 
-- leaving out x : (Fin (S n))

miss : {n:Nat} -> Fin (S n) -> Fin n -> Fin (S n)

miss {n=Z}      _ x = FinZElim x
miss {n=(S n')} m x = if m <= (weaken x) then FS x else weaken x

-- double x is the function Fin (S n) -> Fin n that maps two
-- consecutive values to x : Fin n and is strictly increasing otherwise

double : {n:Nat} -> Fin n -> Fin (S n) -> Fin n

double {n=Z}      x        _     = FinZElim x
double {n=(S n')} _        FZ    = FZ
double {n=(S n')} FZ      (FS x) = x
double {n=(S n')} (FS d') (FS x) = FS ( double {n=n'} d' x )

-- can we define double in a manner similar to miss ?

-- properties of miss and double:

-- missInj : {n:Nat} -> {x:Fin (S n)} -> Injective (miss x)





