module Injective

-- injective functions
-- different equivalent definitions

import Fiber
import Unique
import Control.Isomorphism

-----------------------------------
-- basic definition of Injectivity
-----------------------------------

Injective : (f:a->b) -> Type
Injective {a} f = (x:a) -> (y:a) -> (f x =  f y) -> x = y

-- some basic properties

-- - composition of injectives is injective

compInjIsInj : {f:b->c} -> 
               {g:a->b} -> 
               Injective f -> 
               Injective g -> 
               Injective (f . g)

compInjIsInj {f} {g} fInj gInj x y pEq = 
  gInj x y (fInj (g x) (g y) pEq)

-- - f . g injective => g injective

gInjIfFGInj :  {f:b->c} -> 
               {g:a->b} -> 
               Injective (f . g) -> 
               Injective g

gInjIfFGInj {f} {g} fgInj x y pEq = 
  fgInj x y (cong pEq)

--------------------------------------------------------
-- another definition: all fibers are mere propositions
--------------------------------------------------------

InjectiveF : (f:a->b) -> Type
InjectiveF f = Unique1 (fiber f)

-- equivalence Injective <-> InjectiveF


-- isoInjInjF : (f:a->b) -> Iso (Injective f) (InjectiveF f)
-- isoInjInjF f = MkIso to from toFrom fromTo where
--   to     : (Injective f)  -> (InjectiveF f)
--   to fInj v ( x ** fxEqv ) (y ** fyEqv) 
--   from   : (InjectiveF f) -> (Injective f)
--   toFrom : (pf:(InjectiveF f)) -> to (from pf) = pf
--   fromTo : (pf:(Injective f)) -> from (to pf)  = pf



