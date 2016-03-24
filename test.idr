import Data.Fin
import Control.Isomorphism
import Fiber
import Unique
import Injective
import FinSupp

-- Surjective Functions

data Surjective : (f:a->b) -> Type where
  SurjBy : {f:a->b} -> ((y:b) -> (fiber f y)) -> 
           Surjective {a} {b} f

-- endofunctions on finite sets are injective iff surjective

finEndoSurjIfInj : {n:Nat} -> {f:(Fin n)->(Fin n)} -> Injective f -> Surjective f

finEndoSurjIfInj {n=Z} {f}
  (InjBy {a = (Fin Z)} {b = (Fin Z)} {f} fInj) = SurjBy {f} FinZElim
finEndoSurjIfInj {n = (S n')} {f}
  (InjBy {a = (Fin n)} {b = (Fin n)} {f} fInj) = SurjBy {f} ?surjBy
-- idea: i) fiber over (f FZ) contains FZ
--      ii) if f FZ = FZ , f' = double FZ . (f . FS) is Injective, so Surj by IH,
--          and if x is in fiber f' y then FS x is in fiber f y
--     iii) if f FZ = FS x', f' = (double x') . f . FS is Inj, so Surj by IH,
--          and if x is in fiber f' y then FS x is in fiber f y



-- "total space" of fibration

totalSpace : (f:a->b) -> Type
totalSpace {a} {b} f = Sigma b p where
  p y = fiber f y

totalSpace2 : (f:a->b) -> Type
totalSpace2 {a} {b} f = Sigma (a,b) p where
  p (x,y) = (f x) = y


-- "total space" of the fibration of a map f: a -> b
-- isomorphic to a

-- preparations:
---- uip:
uip : {x:a} -> {y:b} -> (p:(x=y)) -> (q:(x=y)) -> (p = q)
uip Refl Refl = Refl

-- projections from Sigma-Types

pr1 : {a:Type} -> {P:a->Type} -> Sigma a P -> a
pr1 (x ** _) = x

pr2 : {a:Type} -> {P:a->Type} -> (s: Sigma a P) -> P (pr1 s)
pr2 (x ** y) = y

canSigma : {a:Type} -> {P:a->Type} -> (s:Sigma a P) ->
           s = ( (pr1 s) ** (pr2 s) )
canSigma ( x ** y ) = Refl

---- equality in Sigma-Types

total mkEqSigma : {a:Type} -> {p:a->Type} -> {x:a} -> {y:a}
         -> {s:(p x)} -> {t:(p y)}
         -> (p:(x=y)) -> (q:(replace p s)=t)
         -> ((x ** s) = (y ** t))
mkEqSigma Refl Refl = Refl

-- path concatenation

total pconc : {a:Type} -> {x:a} -> {y:a} -> {z:a} -> (p:x=y) -> (q:y=z) -> (x=z)
pconc Refl Refl = Refl

reflRightId : {a:Type} -> {x:a} -> {y:a} -> (p:(x=y)) -> pconc p Refl = p
reflRightId Refl = Refl

reflLeftId : {a:Type} -> {x:a} -> {y:a} -> (p:(x=y)) -> pconc Refl p = p
reflLeftId Refl = Refl

-- how replace acts on the "fiber f" family

repOnFiber : {a:Type} -> {b:Type} -> {f:(a->b)} -> {y:b} -> {y':b} -> 
             (p:y=y') -> (s:(fiber f y)) ->  
             ((replace {a = b} {P = (fiber f)} p s) = 
               ( (pr1 s) ** (pconc (pr2 s) p) ))
repOnFiber Refl s = pconc p1 (cong p2) where
      p1 : s = ( (pr1 s) ** (pr2 s))
      p1 = canSigma s
      p2 : (pr2 s) = (pconc (pr2 s) Refl)
      p2 = sym (reflRightId (pr2 s))


isoTotalA : (f:a->b) -> Iso a (totalSpace f)
isoTotalA {a} {b} f =
  MkIso to from toFrom fromTo where
    to : a -> totalSpace f
    to x = ((f x) ** ( x ** Refl ))
    from : totalSpace f -> a
    from ( y ** ( x ** p)) = x
    toFrom : (z : totalSpace f) -> to (from z) = z
    toFrom (y ** (x ** pf)) = tf where
      tf = mkEqSigma pf  ?pf2 --(pconc ?p1 p2) where
--        p1 : replace {a = b} {x = (f x)} {y} pf ( x ** Refl ) = ( x ** (pconc Refl pf) )
--        p1 = ?pp1
--        p1 = repOnFiber pf ( x ** Refl )
--        p2 : (MkSigma {a} x (pconc {a=b} Refl pf)) = MkSigma {a} x  pf
--        p2 = cong (reflLeftId {a = b} {x=(f x)} {y} pf)
    fromTo : (x : a) -> from (to x) = x
    fromTo _ = Refl






