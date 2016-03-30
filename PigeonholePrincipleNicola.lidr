> module PigeonholePrinciple

> import Data.Fin
> import Data.Vect
> import Syntax.PreorderReasoning

> import Basics
> import NatProperties


> %default total
> %auto_implicits off
> %access public export


Injectivity (of |flip index|):

> ||| Injectivity (one direction)
> Injective1 : {n : Nat} -> {A : Type} -> Vect n A -> Type
> Injective1 {n} xs = (i : Fin n) -> (j : Fin n) -> index i xs = index j xs -> i = j

> ||| Injectivity (the other direction)
> Injective2 : {n : Nat} -> {A : Type} -> Vect n A -> Type
> Injective2 {n} xs = (i : Fin n) -> (j : Fin n) -> Not (i = j) -> Not (index i xs = index j xs)

> ||| Non injectivity, constructive
> NonInjective : {n : Nat} -> {A : Type} -> Vect n A -> Type
> NonInjective {n} xs = (i : Fin n ** (j : Fin n ** (Not (i = j) , index i xs = index j xs)))


Surjectivity (of |flip index|):

> ||| Surjectivity
> Surjective : {n : Nat} -> {A : Type} -> Vect n A -> Type
> Surjective {n} {A} xs = (a : A) -> (i : Fin n ** index i xs = a)


> ||| Non surjectivity, constructive
> NonSurjective : {n : Nat} -> {A : Type} -> Vect n A -> Type
> NonSurjective {n} {A} xs = (a : A ** (i : Fin n) -> Not (index i xs = a))


Relationships of injectivity notions

> ||| Injective1 implies Injective2
> injectiveLemma : {n : Nat} -> {A : Type} -> {xs : Vect n A} -> Injective1 xs -> Injective2 xs
> injectiveLemma i1xs i j contra = contra . (i1xs i j)


Properties of constructive proofs

> ||| NonInjective => Not Injective
> nonInjectiveNotInjective : {n : Nat} -> {A : Type} -> {xs : Vect n A} -> NonInjective xs -> Not (Injective1 xs)
> nonInjectiveNotInjective (i ** (j ** (nieqj , iixseqijxs))) = \ ixs => nieqj (ixs i j iixseqijxs)

> ||| NonSurjective => Not Surjective
> nonSurjectiveNotSurjective : {n : Nat} -> {A : Type} -> {xs : Vect n A} -> NonSurjective xs -> Not (Surjective xs)
> nonSurjectiveNotSurjective (a ** fainiixseqa) = \ sxs => let i = (fst (sxs a)) in (fainiixseqa i) (snd (sxs a))


Properties of constructive proofs (finite case)


> -- should be constructible via lookup table: if for all |k : Fin n| we
> -- have that |k| is in |ks|, we have a table of proofs and we can
> -- construct |Surjective ks| via |lookup|. If we find a |k| which is
> -- not in |ks|, we can construct |NonSurjective ks|.
> finSurjectiveLemma : {n : Nat} -> (ks : Vect n (Fin n)) -> Either (Surjective ks) (NonSurjective ks)
> finSurjectiveLemma Nil       = Left (\ k => absurd k) 
> finSurjectiveLemma (k :: ks) = ?hole1

> -- lala : {n : Nat} -> (ks : Vect n (Fin (S n))) -> NonSurjective ks

> lula :  {m : Nat} -> {n : Nat} -> (k : Fin n) -> (ks : Vect m (Fin n)) -> NonInjective ks -> NonInjective (k :: ks)

> -- 
> finSurjectiveInjectiveLemma : {n : Nat} -> (ks : Vect n (Fin n)) -> NonSurjective ks -> NonInjective ks
> finSurjectiveInjectiveLemma {n = Z}    Nil      (i ** _) = absurd i
> finSurjectiveInjectiveLemma {n = S m} (k :: ks) (i ** p) = ?pulj


> ||| Pigeonhole principle (the S case):
> php : {n : Nat} -> (ks : Vect (S (S n)) (Fin (S n))) -> NonInjective ks
> php {n = Z} (k1 :: k2 :: Nil) = (i ** (FS j ** (p, q))) where
>   i : Fin (S (S Z))
>   i = FZ
>   j : Fin (S Z)
>   j = FZ
>   p : Not (i = FS j)
>   p = FZNotFS
>   q : index i (k1 :: k2 :: Nil) = index (FS j) (k1 :: k2 :: Nil)
>   q = ?lilk
> php {n = S m} (k :: ks) with (finSurjectiveLemma ks)
>   | (Left   sks) = (i ** (FS j ** (p, q))) where
>     i : Fin (S (S (S m)))
>     i = FZ
>     j : Fin (S (S m))
>     j = fst (sks k)
>     o : index j ks = k
>     o = snd (sks k)
>     p : Not (i = FS j)
>     p = FZNotFS
>     q : index i (k :: ks) = index (FS j) (k :: ks)
>     q = ( index i (k :: ks) )
>       ={ Refl }=
>         ( k )
>       ={ sym o }=
>         ( index j ks )
>       ={ Refl }=
>         ( index (FS j) (k :: ks) )
>       QED
>   | (Right nsks) = lula k ks (finSurjectiveInjectiveLemma ks nsks)


> {-

> ---}


