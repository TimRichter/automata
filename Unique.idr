module Unique

%default total

-- mere propositions... 
-- called Unique here to be consistent with nicola's SeqDecProbs

Unique : Type -> Type
Unique t = (p:t) -> (q:t) -> p=q

Unique1 : (t0 -> Type) -> Type
Unique1 {t0} t1 = (v : t0) -> Unique (t1 v)

-- UIP holds in idris, i.e. any Equality Type is Unique

uip : {a:Type} -> {x:a} -> {y:a} -> Unique (x=y)
uip Refl Refl = Refl

uipH : {A, B : Type} -> {x : A} -> {y : B} ->
       (A = B) -> Unique (x = y)
uipH Refl Refl Refl = Refl


