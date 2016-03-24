> module PigeonHole2

> import Data.Vect
> import Data.Fin
> import Control.Isomorphism

> %default total

PigeonHole principle in vector form:

We want to prove

< pigeonHole :  {m, n : Nat} -> (m `LT` n) -> (xs : Vect n (Fin m)) -> 
<               Repeats xs

where elements of (Repeats xs) prove (constructively) that elements at 
two different indices of xs are equal. 

We need type families

> data Appears : {A : Type} -> {n : Nat} -> 
>                A -> (Vect n A) -> Type where
>
>     App_head : {A : Type} -> {n : Nat} -> 
>                (x, y : A) -> (ys : Vect n A) -> 
>                (x = y) ->      Appears x (y :: ys)
>
>     App_tail : {A : Type} -> {n : Nat} -> 
>                (x, y : A) -> (ys : Vect n A) ->
>                Appears x ys -> Appears x (y :: ys)

> data Repeats : {A : Type} -> {n : Nat} -> 
>                (xs : Vect n A) -> Type where
>
>     Rep_head : {A : Type} -> {n : Nat} -> 
>                (x : A) -> (xs : Vect n A) -> 
>                Appears x xs -> Repeats (x :: xs)
>
>     Rep_tail : {A : Type} -> {n : Nat} -> 
>                (x : A) -> (xs : Vect n A) ->
>                Repeats xs -> Repeats (x :: xs)

and some lemmata:



Appears is decidable if equality in A is:

> decAppears : {A : Type} -> (DecEq A) => {n : Nat} -> 
>              (x : A) -> (xs : Vect n A) -> 
>              (Dec (Appears x xs))
>
> decAppears x Nil = No (prf x) where
>     prf : {A : Type} -> (x : A) -> 
>           Appears x Nil -> Void
>     prf _ (App_head _ _ _ _) impossible
>     prf _ (App_tail _ _ _ _) impossible
> decAppears x (y :: ys) 
>     with (decEq x y)
>     | (Yes xEqy)  = Yes (App_head x y ys xEqy)
>     | (No  xNeqy) 
>       with (decAppears x ys)
>       | (Yes xInys)    = Yes (App_tail x y ys xInys)
>       | (No  xNotinys) = No prf2 where
>           prf2 (App_head _ _ _ xEqy)  = xNeqy xEqy
>           prf2 (App_tail _ _ _ xInys) = xNotinys xInys



Repeats is decidable if equality in A is:

> decRepeats : {A : Type} -> (DecEq A) => {n : Nat} -> 
>              (xs : Vect n A) -> Dec (Repeats xs)
>
> decRepeats Nil = No nilNotRepeats where
>     nilNotRepeats (Rep_head _ _ _) impossible
>     nilNotRepeats (Rep_tail _ _ _) impossible
> decRepeats (x :: xs) 
>     with (decAppears x xs)
>     | (Yes xInxs)    = Yes (Rep_head x xs xInxs)
>     | (No  xNotinxs) 
>       with (decRepeats xs)
>       | (Yes xsRepeats)    = Yes (Rep_tail x xs xsRepeats)
>       | (No  xsNotRepeats) = No xxsNotRepeats where
>         xxsNotRepeats (Rep_head _ _ xInxs)     = xNotinxs xInxs
>         xxsNotRepeats (Rep_tail _ _ xsRepeats) = xsNotRepeats xsRepeats



If x doesn't appear in (y :: ys), it doesn't appear in ys:

> notAppearsTail : {A : Type} -> {n : Nat} -> 
>                  (x, y : A) -> (ys : Vect n A) ->
>                  Not (Appears x (y :: ys)) -> 
>                  Not (Appears x ys)
>
> notAppearsTail x y ys xNotInyys xInys = 
>     xNotInyys (App_tail x y ys xInys)



"Functoriality" of Appears:

> functAppears : {A, B : Type} -> {n : Nat} -> 
>                (f : A -> B) -> (x : A) -> (ys : Vect n A) ->
>                Appears x ys -> Appears (f x) (map f ys)
>
> functAppears f x Nil     (App_head _ _ _ _) impossible
> functAppears f x (y :: ys) (App_head _ _ _ xEqy) = 
>     App_head (f x) (f y) (map f ys) fxEqfy where
>       fxEqfy : f x = f y
>       fxEqfy = cong xEqy
> functAppears f x Nil     (App_tail _ _ _ _) impossible
> functAppears f x (y :: ys) (App_tail _ _ _ xInys) = 
>     App_tail (f x) (f y) (map f ys) fxInfys where
>       fxInfys : Appears (f x) (map f ys)
>       fxInfys = functAppears f x ys xInys



"Functoriality" of Repeats:

> functRepeats : {A, B : Type} -> {n : Nat} -> 
>                (f : A -> B) -> (xs : Vect n A) -> 
>                Repeats xs -> Repeats (map f xs)
>
> functRepeats f (x :: xs) (Rep_head _ _ xInxs) = 
>     Rep_head (f x) (map f xs) fxInfxs where
>        fxInfxs : Appears (f x) (map f xs)
>        fxInfxs = functAppears f x xs xInxs
> functRepeats f (x :: xs) (Rep_tail _ _ repeatsxs) =
>     Rep_tail (f x) (map f xs) repeatsfxs where
>        repeatsfxs : Repeats (map f xs)
>        repeatsfxs = functRepeats f xs repeatsxs



If an element is inserted somewhere in a Vect, it 
appears in the result:

> insAppears : {A : Type} -> {n : Nat} -> 
>              (k : Fin (S n)) -> (x : A) -> (ys : Vect n A) ->
>              Appears x (insertAt k x ys)
>
> insAppears FZ     x  ys       = App_head x x ys Refl
> insAppears (FS k) x  Nil      = absurd k
> insAppears (FS k) x (y :: ys) = 
>     App_tail x y (insertAt k x ys) (insAppears k x ys)



If an element that already appears is inserted again, the 
resulting vector will have a repeat:

> insAppRepeats : {A : Type} -> {n : Nat} -> 
>                 (k : Fin (S n)) -> (x : A) -> (ys : Vect n A) ->
>                 Appears x ys -> Repeats (insertAt k x ys)
>
> insAppRepeats _ _ Nil (App_head _ _ _ _) impossible
> insAppRepeats _ _ Nil (App_tail _ _ _ _) impossible
> insAppRepeats FZ     x (y :: ys) xInyys = 
>     Rep_head x (y :: ys) xInyys
> insAppRepeats (FS k) x (y :: ys) (App_head _ _ _ xEqy) =
>     Rep_head y (insertAt k x ys) yInInsert where
>       yInInsert : Appears y (insertAt k x ys)
>       yInInsert = replace {P = \z => Appears z (insertAt k x ys)} 
>                           xEqy (insAppears k x ys)
> insAppRepeats (FS k) x (y :: ys) (App_tail _ _ _ xInys) = 
>     Rep_tail y (insertAt k x ys) (insAppRepeats k x ys xInys)



If x appears in ys and y is inserted, x still appears in the result:

> insKeepsApp : {A : Type} -> {n : Nat} -> 
>               (k : Fin (S n)) -> (x, y : A) -> (ys : Vect n A) ->
>               Appears x ys -> Appears x (insertAt k y ys)
>
> insKeepsApp FZ      x y ys xInys = 
>     App_tail x y ys xInys
> insKeepsApp (FS k') x y (z :: ys) (App_head _ _ _ xEqz)  = 
>     App_head x z (insertAt k' y ys) xEqz
> insKeepsApp (FS k') x y (z :: ys) (App_tail _ _ _ xInys) = 
>     App_tail x z (insertAt k' y ys) xInIns where
>       xInIns = insKeepsApp k' x y ys xInys



If xs has a repeat, xs with another element inserted still has a repeat

> insKeepsRep : {A : Type} -> {n : Nat} -> 
>               (k : Fin (S n)) -> (x : A) -> (ys : Vect n A) ->
>               Repeats ys -> Repeats (insertAt k x ys)
>
> insKeepsRep FZ      x  ys     repys = 
>     Rep_tail x ys repys
> insKeepsRep (FS k') x (y :: ys) (Rep_head _ _ yInys) = 
>     Rep_head y (insertAt k' x ys) yInIns where
>       yInIns : Appears y (insertAt k' x ys)
>       yInIns = insKeepsApp k' y x ys yInys
> insKeepsRep (FS k') x (y :: ys) (Rep_tail _ _ repys) = 
>     Rep_tail y (insertAt k' x ys) repIns where
>       repIns : Repeats (insertAt k' x ys)
>       repIns = insKeepsRep k' x ys repys



Remove an appearing element from a vector, along with the rest vector
return an index and a proof that inserting the removed element at
that index into the rest vector gives back the original vector:

> removeAppearing : {A : Type} -> {n : Nat} -> 
>                   (x : A) -> (ys : Vect (S n) A) ->
>                   Appears x ys -> 
>                   ( ys' : Vect n A ** 
>                       ( k : Fin (S n) ** 
>                           (insertAt k x ys') = ys 
>                       )
>                   )
>
> removeAppearing x (y :: ys) (App_head _ _ _ xEqy) = 
>     ( ys ** ( FZ ** xysEqyys )) where
>       xysEqyys : (x :: ys) = (y :: ys)
>       xysEqyys = cong {f = \z => z :: ys} xEqy
> removeAppearing {n=Z} _ _ (App_tail _ _ _ (App_head _ _ _ _)) impossible
> removeAppearing {n=Z} _ _ (App_tail _ _ _ (App_tail _ _ _ _)) impossible
> removeAppearing {n=(S _)} x (y :: ys) (App_tail _ _ _ xInys) 
>     with (removeAppearing x ys xInys) 
>     | (ys' ** (k' ** prf'))  = 
>       ((y :: ys') ** ((FS k') ** prf)) where
>         prf : insertAt (FS k') x (y :: ys') = (y :: ys)
>         prf  = cong {f = \zs => y :: zs} prf'



Specifically for (Fin n) vectors
If FZ does not appear in a vector xs over (Fin (S n)), 
xs is map FS xs' for some vector xs' over (Fin n):

> finVectFromBelow : {n, m : Nat} -> (xs : Vect m (Fin (S n))) -> 
>                    Not (Appears FZ xs) -> 
>                    (zs : (Vect m (Fin n)) ** map FS zs = xs)
>
> finVectFromBelow Nil            _          = (Nil ** Refl)
> finVectFromBelow ( FZ    :: xs) fzNotInxxs = 
>     void (fzNotInxxs (App_head FZ FZ xs Refl))
> finVectFromBelow ((FS z) :: xs) fzNotInxxs 
>     with (finVectFromBelow xs (notAppearsTail FZ (FS z) xs fzNotInxxs))
>     | (zs ** mapFSzsEqxs) = ((z :: zs) ** mapFSzzsEqxxs) where
>       mapFSzzsEqxxs  : map FS (z :: zs) = ((FS z) :: xs)
>       mapFSzzsEqxxs  = cong {f = \ys => (FS z) :: ys} mapFSzsEqxs




Finally:

> pigeonHole : {n, m : Nat} -> (n `LT` m) -> (xs : Vect m (Fin n)) -> 
>              Repeats xs
>
> -- impossible cases:
> pigeonHole {m=Z}      LTEZero    _   impossible
> pigeonHole {m=Z}     (LTESucc _) _   impossible
> pigeonHole {m=(S _)}  _          Nil impossible
> -- Fin Z is Void:
> pigeonHole {n=Z}      _ (x :: _) = absurd x
> -- the interesting case:
> pigeonHole {n=(S p)} {m=(S q)} (LTESucc pLTq) xs 
>      with (decRepeats xs)
>      | (Yes xsRepeats)    = xsRepeats
>      | (No  xsNotRepeats) 
>        with (decAppears FZ xs)
>        | (Yes fzInxs)     
>           with (removeAppearing FZ xs fzInxs)
>           | (zs ** (k ** inskfzzsEqxs)) 
>              with (decAppears FZ zs)
>              | (Yes fzInzs) = void (xsNotRepeats xsRepeats) where
>                 xsRepeats : Repeats xs
>                 xsRepeats = replace inskfzzsEqxs (insAppRepeats k FZ zs fzInzs)
>              | (No  fzNotInzs) 
>                 with (finVectFromBelow zs fzNotInzs)
>                 | (zs' ** mapFSzs'Eqzs) = void (xsNotRepeats xsRepeats) where
>                     zs'Repeats : Repeats zs'
>                     zs'Repeats = pigeonHole pLTq zs'
>                     zsRepeats : Repeats zs
>                     zsRepeats = replace mapFSzs'Eqzs (functRepeats FS zs' zs'Repeats)
>                     xsRepeats : Repeats xs
>                     xsRepeats = replace inskfzzsEqxs (insKeepsRep k FZ zs zsRepeats)
>        | (No  fzNotInxs) 
>           with (finVectFromBelow xs fzNotInxs) 
>           | (xs' ** mapFSxs'Eqxs) = void (xsNotRepeats xsRepeats) where
>               xs'Repeats : Repeats xs'
>               xs'Repeats = pigeonHole (lteSuccRight pLTq) xs'
>               xsRepeats : Repeats xs
>               xsRepeats = replace mapFSxs'Eqxs (functRepeats FS xs' xs'Repeats)




An equivalent, but maybe more useful version of Repeats
as an iterated Sigma-Type:

For preparation, we need a type for expressing that i < j for
i, j : Fin n

> data LTEF  : {n : Nat} -> (i, j : Fin n) -> Type where
>   ||| Zero is the smallest 
>   LTEFZero : {n : Nat} -> LTEF {n=(S n)} FZ    right
>   ||| If n <= m, then n + 1 <= m + 1
>   LTEFSucc : LTEF left right -> LTEF (FS left) (FS right)

> implementation Uninhabited (LTEF (FS n) FZ) where
>   uninhabited LTEFZero impossible

 ||| Greater than or equal to
 total GTE : Nat -> Nat -> Type
 GTE left right = LTE right left

> ||| Strict less than
> total LTF : {n : Nat} -> (i, j : Fin n) -> Type
> LTF left right = LTEF (FS left) (weaken right)

||| Strict greater than
total GT : Nat -> Nat -> Type
GT left right = LT right left

> ||| A successor is never less than or equal zero
> succNotLTEFzero : Not (FS m `LTEF` FZ)
> succNotLTEFzero LTEFZero impossible

> ||| If two numbers are ordered, their predecessors are too
> fromLteFSucc : (FS i `LTEF` FS j) -> (i `LTEF` j)
> fromLteFSucc (LTEFSucc x) = x

> ||| A decision procedure for `LTE`
> isLTEF : {n : Nat} -> (i, j : Fin n) -> Dec (i `LTEF` j)
> isLTEF FZ j = Yes LTEFZero
> isLTEF (FS i) FZ = No succNotLTEFzero
> isLTEF (FS i) (FS j) with (isLTEF i j)
>   | (Yes prf) = Yes (LTEFSucc prf)
>   | (No contra) = No (contra . fromLteFSucc)

> ||| `LTEF` is reflexive.
> lteFRefl : {n : Nat} -> {i : Fin n} -> LTEF i i
> lteFRefl {i = FZ}  = LTEFZero
> lteFRefl {i = FS k} = LTEFSucc lteFRefl

> ||| n < m implies n < m + 1
> lteFSRight : LTEF i j -> LTEF (weaken i) (FS j)
> lteFSRight LTEFZero       = LTEFZero
> lteFSRight (LTEFSucc prf) = LTEFSucc (lteFSRight prf)



> Appears' : {A : Type} -> {n : Nat} ->
>            A -> (Vect n A) -> Type 
> Appears' {A} {n} x xs = ( i : Fin n ** x = index i xs )


> Repeats' : {A : Type} -> {n : Nat} ->
>            (xs : Vect n A) -> Type
>      
> Repeats' {A} {n} xs = 
>   ( i : Fin n ** (j : Fin n ** (i `LTF` j , index i xs = index j xs)))


we show that these are isomorphic to the versions above

> toA : {A : Type} -> {n : Nat} -> 
>       (x : A) -> (xs : Vect n A) ->
>       Appears x xs -> Appears' x xs
>
> toA x (y::ys) (App_head _ _ _ xEqy) = (FZ ** xEqy)
> toA x (y::ys) (App_tail _ _ _ xInys) 
>   with (toA x ys xInys)
>   | (j ** xEqysj) = ((FS j) ** xEqysj) 


> fromA : {A : Type} -> {n : Nat} -> 
>         (x : A) -> (xs : Vect n A) ->
>         Appears' x xs -> Appears x xs
>
> fromA x (y::ys) (FZ ** xEqy) = App_head x y ys xEqy
> fromA x (y::ys) ((FS j) ** xEqysj) = App_tail x y ys (fromA x ys (j ** xEqysj))

> toFromA : {A : Type} -> {n : Nat} -> 
>           (x : A) -> (xs : Vect n A) ->
>           (p : Appears' x xs) -> toA x xs ((fromA x xs) p) = p
>
> toFromA x (y::ys) (FZ ** xEqy) = Refl
> toFromA x (y::ys) ((FS j) ** xEqysj) =
>     (toA x (y::ys) (fromA x (y::ys) ((FS j) ** xEqysj)))           ={ Refl }=
>     (toA x (y::ys) (App_tail x y ys (fromA x ys (j ** xEqysj))))   ={ ?lala }=
>     ((FS j) ** xEqysj)                                             QED                 




with (toFromA x ys (j ** xEqysj))








> toR : {A : Type} -> {n : Nat} -> (xs: Vect n A) -> Repeats xs -> Repeats' xs
>
> toR Nil        (Rep_head _ _ _) impossible
> toR Nil        (Rep_tail _ _ _) impossible
> toR (_::Nil)   (Rep_head _ _ (App_head _ _ _ _)) impossible
> toR (_::Nil)   (Rep_head _ _ (App_tail _ _ _ _)) impossible
> toR (x::y::ys) (Rep_head _ _ (App_head _ _ _ xEqy))  
>         = ( FZ ** ( FS (FZ) ** ((LTEFSucc LTEFZero), xEqy)))
> toR (x::y::ys) (Rep_head _ _ (App_tail _ _ _ xInys)) 
>     with (toR (x::ys) (Rep_head x ys xInys))
>     | (FZ ** ((FS j) ** ( _ , xEqxysj))) 
>         = (FZ ** ((FS (FS j)) ** ((LTEFSucc LTEFZero), xEqxysj)))
>     | (FZ ** (FZ ** ( fsFZLTEFFZ , _)))
>         = void (succNotLTEFzero fsFZLTEFFZ)
> toR (x::xs)    (Rep_tail _ _ repeatsxs) 
>     with (toR xs repeatsxs)
>     | (i ** (j ** ( iLTFj, xsiEqxsj )))
>         = ((FS i) ** ( (FS j) ** ( (LTEFSucc iLTFj) , xsiEqxsj)))


 repeatsIso : {A : Type} -> {n : Nat} -> 
              (xs : Vect n A) -> Iso (Repeats xs) (Repeats' xs)
 repeatsIso xs = MkIso (to xs) (from xs) (toFrom xs) (fromTo xs) where
   to     : {A : Type} -> {n : Nat} -> 
            (xs: Vect n A) -> Repeats xs -> Repeats' xs
   from   : {A : Type} -> {n : Nat} -> 
            (xs: Vect n A) -> Repeats' xs -> Repeats xs
   toFrom : {A : Type} -> {n : Nat} -> 
            (xs: Vect n A) -> (p : Repeats' xs) -> (to xs) ((from xs) p) = p
   fromTo : {A : Type} -> {n : Nat} -> 
            (xs: Vect n A) -> (p : Repeats xs) -> (from xs) ((to xs) p) = p

         


      




