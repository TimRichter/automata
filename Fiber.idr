module Fiber

import Control.Isomorphism
import Syntax.PreorderReasoning
import Unique

-- the fibers of a map

fiber : {A:Type} -> {B:Type} -> (f: A->B) -> (y:B) -> Type
fiber {A} {B} f y = Sigma A p where
  p : (x:A) -> Type
  p x = ((f x) = y)

-- Isos

isoMapSigmaFibers : {A:Type} -> {B:Type} -> (f: A -> B) -> 
                    Iso A (Sigma B (fiber {A} {B} f))

isoMapSigmaFibers {A} {B} f = MkIso to from toFrom fromTo where
  to : A -> (Sigma B (fiber {A} {B} f))
  to   a  = ( (f a) ** ( a ** Refl))
  from : (Sigma B (fiber {A} {B} f)) -> A
  from (b ** (a ** faisb))   = a
  fromTo a                   = Refl
  toFrom (b ** (a ** faisb)) = ?lala

--    ( (f a) ** ( a ** Refl {x=(f a)}))   ={ ?step1 }= --cong {f = \x => (x ** (a ** Refl {x}))} faisb }=
--      ( b     ** ( a ** Refl {x=b}))     ={ ?step2 }= -- cong {f = \p => (b ** (a ** p))} (uipH (cong {f = \x => x = b} faisb) Refl faisb) }=
--    ( b     ** ( a ** faisb ))           QED

-- let's test wether indeed an equality in the
-- base of a type family suffices to show the
-- equality of the respective fiber types

famEq : {A:Type} -> (P:A -> Type) ->
        (x:A) -> (y:A) -> (eq:x=y) -> (P x) = (P y)
famEq {A} P x y eq = cong eq









