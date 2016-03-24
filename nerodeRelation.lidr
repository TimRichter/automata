> module NerodeRelation
>
> %default total

Here we take a language over some alphabet a to
be an arbitrary type family over (List a).

Propositionality or even decidability shall only
be assumed if needed...

> Lang : Type -> Type
> Lang a = (List a) -> Type

A logical equivalence of two types is just a pair of
functions

> LogEq : Type -> Type -> Type
> LogEq a b = (a -> b, b -> a)

this is an equivalence relation on types

> logEqRefl : (a : Type) -> LogEq a a
> logEqRefl a = (id, id)

> logEqSym : {a, b : Type} -> LogEq a b -> LogEq b a
> logEqSym (f,g) = (g,f)

> logEqTrans : {a, b, c : Type} -> LogEq a b -> LogEq b c -> LogEq a c
> logEqTrans (aTob,bToa) (bToc,cTob) = (bToc . aTob, bToa . cTob)

Definition of the Nerode relation

> Nerode : {a : Type} -> Lang a -> (List a) -> (List a) -> Type
> Nerode L as bs = (cs : List a) -> LogEq (L (as++cs)) (L (bs++cs))

The Nerode Relation is an equivalence Relation:

> nerodeRefl : {a : Type} -> (L : Lang a) -> (as : List a) ->
>              Nerode L as as
> nerodeRefl L as cs = logEqRefl (L (as++cs))

> nerodeSym : {a : Type} -> (L : Lang a) -> (as, bs : List a) ->
>             Nerode L as bs -> Nerode L bs as
> nerodeSym L as bs asNRbs cs = logEqSym (asNRbs cs)

> nerodeTrans : {a : Type} -> (L : Lang a) -> (as, bs, cs : List a) ->
>               Nerode L as bs -> Nerode L bs cs -> Nerode L as cs
> nerodeTrans L as bs cs asNRbs bsNRcs ds = logEqTrans (asNRbs ds) (bsNRcs ds)

