> import Control.Isomorphism

We characterize the equality (paths) type of two elements
of a Sigma type as a Sigma type like in HoTT:

Proof can be simplified with UIP:

> uip : {a:Type} -> {x:a} -> {y:a} -> (p:(x=y)) -> (q:(x=y)) -> (p=q)
> uip Refl Refl = Refl

dependent cong

> congD : {A : Type} -> {P : A -> Type} ->
>         (f : (a : A) -> P a) -> {x, y : A} ->
>         (x = y) -> (f x = f y)
> congD f Refl = Refl


> congD2 : {A : Type} -> {P : A -> Type} ->
>         (f : (a : A) -> P a) -> {x, y : A} ->
>         (p : x = y) -> (replace p (f x) = f y)
> congD2 f Refl = Refl


> sigmaEq1 : {A : Type} -> {P : A -> Type} ->
>         {x, y : A} -> (px : P x) ->
>         (p : x = y) -> ((x ** px) = (y ** replace p px))
> sigmaEq1 px Refl = Refl


 sigmaEq2 : {A : Type} -> {P : A -> Type} ->
            {x, y : A} -> (px : P x) ->
            (p : x = y) -> ((x ** px) = (y ** replace p px))
 sigmaEq2 px Refl = Refl


 eqSigmaIsoSigma : {a:Type} -> {P:a->Type} -> {s1:Sigma a P} -> {s2:Sigma a P} ->
     Iso (s1=s2) (Sigma ((getWitness s1)=(getWitness s2)) 
         (\ eqW => (replace eqW (getProof s1))=(getProof s2)))
 eqSigmaIsoSigma {a} {P} {s1} {s2} = MkIso to from toFrom fromTo where
     to : (s1=s2) -> (Sigma ((getWitness s1)=(getWitness s2)) 
                     (\ eqW =>))
