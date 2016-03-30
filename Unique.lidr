> module Unique
>
> import Syntax.PreorderReasoning
>
> %default total
> %auto_implicits off
> %access public export

mere propositions... 
called Unique here 

> Unique : Type -> Type
> Unique A = (p:A) -> (q:A) -> p=q

unique type families

> Unique1 : {A : Type} -> (A -> Type) -> Type
> Unique1 {A} P = (a : A) -> Unique (P a)

UIP holds in idris, i.e. any Equality Type is Unique

> uip : {A : Type} -> {x : A} -> {y : A} -> Unique (x=y)
> uip Refl Refl = Refl

here is a heterogeneous variant

> uipH : {A, B : Type} -> {x : A} -> {y : B} ->
>        (A = B) -> Unique (x = y)
> uipH Refl Refl Refl = Refl

Void is Unique

> voidUnique : Unique Void
> voidUnique v _ = absurd v

The unit type is unique

> unitUnique : Unique ()
> unitUnique () () = Refl

if A and B are unique, so is their
cartesian product

> prodUnique : {A, B : Type} -> 
>              Unique A -> Unique B ->
>              Unique (A , B)
> prodUnique AUni BUni (a,b) (a',b') =  
>   (a  , b )  ={ cong {f = \x => (x , b)}  (AUni a a') }=
>   (a' , b )  ={ cong {f = \y => (a' , y)} (BUni b b') }=
>   (a' , b')  QED

if A and B are unique and their cartesian product is
absurd, their Unit is unique

> disjointSumUnique : {A, B : Type} ->
>                     Unique A -> Unique B ->
>                     Not (A,B) ->
>                     Unique (Either A B)
> disjointSumUnique AUni _ _  (Left a)  (Left a')  = cong (AUni a a')
> disjointSumUnique _ _ notAB (Left a)  (Right b)  = absurd (notAB (a,b))
> disjointSumUnique _ _ notAB (Right b) (Left a)   = absurd (notAB (a,b))
> disjointSumUnique _ BUni _  (Right b) (Right b') = cong (BUni b b')











