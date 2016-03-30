> module FinSub
> import Unique 
>
> %default total
> %auto_implicits off
> %access public export

A Subset of a type A is just a 
Unique type family P on a

> SubSet : Type -> Type
> SubSet A = (P : (A -> Type) ** (a : A) -> Unique (P a))

here's the empty subset

> emptySub : {A : Type} -> SubSet A
> emptySub {A} = (\a => Void ** \a => voidUnique)

the full subset

> fullSub : {A : Type} -> SubSet A
> fullSub {A} = (\a => () ** \a => unitUnique)


operations on SubSets of A




