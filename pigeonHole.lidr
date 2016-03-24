> module PigeonHole

> import Data.Fin
> import Data.Vect
> import Syntax.PreorderReasoning

> %default total

PigeonHole principle in vector form:

We want to prove

< pigeonHole :  {n, m : Nat} -> (n `LT` m) -> (xs : Vect m (Fin n)) -> 
<               Repeats xs

where elements of (Repeats xs) prove (constructively) that elements at 
two different indices of xs are equal. 

For preparation, we need a type for expressing that i < j for
i, j : Fin n

> data LTEF  : {n : Nat} -> Fin n -> Fin n -> Type where
>   ||| Zero is the smallest 
>   LTEFZero : {n : Nat} -> LTEF {n=(S n)} FZ    right
>   ||| If n <= m, then n + 1 <= m + 1
>   LTEFSucc : LTEF left right -> LTEF (FS left) (FS right)

> implementation Uninhabited (LTEF (FS n) FZ) where
>   uninhabited LTEFZero impossible

> ||| Greater than or equal to
> total GTEF : {n : Nat} -> Fin n -> Fin n -> Type
> GTEF left right = LTEF right left

> ||| Strict less than
> total LTF : {n : Nat} -> Fin n -> Fin n -> Type
> LTF left right = LTEF (FS left) (weaken right)

||| Strict greater than
total GT : Nat -> Nat -> Type
GT left right = LT right left

> ||| A successor is never less than or equal zero
> succNotLTEFzero : Not (FS m `LTEF` FZ)
> succNotLTEFzero LTEFZero impossible

> ||| If two numbers are ordered, their predecessors are ordered too
> fromLteFSucc : (FS i `LTEF` FS j) -> (i `LTEF` j)
> fromLteFSucc (LTEFSucc x) = x

> ||| A decision procedure for `LTEF`
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

> ||| index i is a natural transformation between Vect n and Id
> |||
> indexNT : {A, B : Type} -> {n : Nat} ->
>              (f : A -> B) -> (xs : Vect n A) -> (i : Fin n) ->
>              index i (map f xs) = f (index i xs)
> indexNT f Nil FZ impossible
> indexNT f Nil (FS _) impossible
> indexNT f (x :: xs) FZ = Refl
> indexNT f (x :: xs) (FS i) 
>   with (indexNT f xs i)
>   | fxsiEqfxsi = fxsiEqfxsi


Now we can define the type families we need

> Appears : {A : Type} -> {n : Nat} ->
>           A -> (Vect n A) -> Type 
> Appears {A} {n} x xs = ( i : Fin n ** x = index i xs )


> Repeats : {A : Type} -> {n : Nat} ->
>           (xs : Vect n A) -> Type
>      
> Repeats {A} {n} xs = 
>   ( i : Fin n ** (j : Fin n ** (i `LTF` j , index i xs = index j xs)))


> ||| Appears is decidable if equality in A is:
> |||
> decAppears : {A : Type} -> (DecEq A) => {n : Nat} -> 
>              (x : A) -> (xs : Vect n A) -> 
>              (Dec (Appears x xs))
>
> decAppears x Nil = No (prf x) where
>     prf : {A : Type} -> (x : A) -> 
>           Appears x Nil -> Void
>     prf _ (FZ ** _)     impossible
>     prf _ ((FS _) ** _) impossible
> decAppears x (y :: ys) 
>     with (decEq x y)
>     | (Yes xEqy)  = Yes (FZ ** xEqy)
>     | (No  xNeqy) 
>       with (decAppears x ys)
>       | (Yes (i ** xEqysi)) = Yes ((FS i) ** xEqysi)
>       | (No  xNotinys) = No prf2 where
>           prf2 (FZ ** xEqy)  = xNeqy xEqy
>           prf2 ((FS i) ** xEqysFSi) = xNotinys (i ** xEqysFSi)


> ||| Repeats is decidable if equality in A is:
> |||
> decRepeats : {A : Type} -> (DecEq A) => {n : Nat} -> 
>              (xs : Vect n A) -> Dec (Repeats xs)
>
> decRepeats Nil = No nilNotRepeats where
>     nilNotRepeats (FZ ** _)   impossible
>     nilNotRepeats (FS _ ** _) impossible
> decRepeats (x :: xs) 
>     with (decAppears x xs)
>     | (Yes (i ** xEqtailxsi)) = Yes (FZ ** ((FS i) ** (LTEFSucc LTEFZero, xEqtailxsi)))
>     | (No  xNotinxs) 
>       with (decRepeats xs)
>       | (Yes (i ** (j ** (iLTj,xsiEqxsj))))    = Yes ((FS i) ** ((FS j) ** (LTEFSucc iLTj, xsiEqxsj)))
>       | (No  xsNotRepeats) = No xxsNotRepeats where
>         xxsNotRepeats (FZ ** (FZ ** (LTEFSucc _ ,_))) impossible
>         xxsNotRepeats (FZ ** ((FS j) ** (_, xEqxsj))) = xNotinxs (j ** xEqxsj)
>         xxsNotRepeats ((FS i) ** ((FS j) ** (LTEFSucc iLTEj, xsiEqxsj))) = xsNotRepeats (i ** (j ** (iLTEj, xsiEqxsj)))


> ||| If x doesn't appear in a vector, it doesn't appear in its tail:
> |||
> notAppearsTail : {A : Type} -> {n : Nat} -> 
>                  (x, y : A) -> (ys : Vect n A) ->
>                  Not (Appears x (y :: ys)) -> 
>                  Not (Appears x ys)
>
> notAppearsTail x y ys xNotInyys (i ** xEqysi) = 
>     xNotInyys ((FS i) ** xEqysi)


> ||| "Functoriality" of Appears:
> |||
> functAppears : {A, B : Type} -> {n : Nat} -> 
>                (f : A -> B) -> (x : A) -> (ys : Vect n A) ->
>                Appears x ys -> Appears (f x) (map f ys)
>
> functAppears f x ys (i ** xEqysi) = (i ** fxEqfysi) where
>   fxEqfysi : f x = index i (map f ys)
>   fxEqfysi = 
>       (f x)                 ={ cong xEqysi }=
>       (f (index i ys))      ={ sym (indexNT f ys i) }=
>       (index i (map f ys))  QED


> ||| "Functoriality" of Repeats:
> |||
> functRepeats : {A, B : Type} -> {n : Nat} -> 
>                (f : A -> B) -> (xs : Vect n A) -> 
>                Repeats xs -> Repeats (map f xs)
>
> functRepeats f xs (i ** (j ** (iLTj, xsiEqxsj))) =
>   (i ** (j ** (iLTj, fxsiEqfxsj))) where
>   fxsiEqfxsj : index i (map f xs) = index j (map f xs)
>   fxsiEqfxsj =
>     (index i (map f xs))   ={ indexNT f xs i }=
>     (f (index i xs))       ={ cong xsiEqxsj     }=
>     (f (index j xs))       ={ sym (indexNT f xs j) }=
>     (index j (map f xs))   QED


> ||| If an element is inserted into a vector,
> ||| it will appear in the result:
> |||
> insAppears : {A : Type} -> {n : Nat} -> 
>              (k : Fin (S n)) -> (x : A) -> (ys : Vect n A) ->
>              Appears x (insertAt k x ys)
>
> insAppears FZ     x  ys       = (FZ ** Refl)
> insAppears (FS k) x  Nil      = absurd k
> insAppears (FS k) x (y :: ys) 
>   with (insAppears k x ys)
>   | (i ** xEqysi) = ((FS i) ** xEqysi)



> ||| If x is inserted in ys at k, the result has x at index k 
> |||
> insertAtIndex : {A : Type} -> {n : Nat} ->
>                 (k : Fin (S n)) -> (x : A) -> (ys : Vect n A) ->
>                 index k (insertAt k x ys) = x
> insertAtIndex FZ     x ys = Refl
> insertAtIndex (FS FZ) x Nil impossible
> insertAtIndex (FS k) x (y :: ys) 
>   with (insertAtIndex k x ys)
>   | inskxyskEqx = inskxyskEqx



> ||| If an element already appearing in a vector is inserted again,
> ||| the result will have a repeat:
> |||
> insAppRepeats : {A : Type} -> {n : Nat} -> 
>                 (k : Fin (S n)) -> (x : A) -> (ys : Vect n A) ->
>                 Appears x ys -> Repeats (insertAt k x ys)
>
> insAppRepeats _ _ Nil (FZ     ** _) impossible
> insAppRepeats _ _ Nil ((FS _) ** _) impossible
> insAppRepeats FZ     x (y :: ys) (j ** xEqyysj) = 
>     (FZ ** ((FS j) ** (LTEFSucc LTEFZero, xEqyysj)))
> insAppRepeats (FS k) x (y :: ys) (FZ ** xEqy) =
>     (FZ ** ((FS k) ** (LTEFSucc LTEFZero, yEqx))) where
>       yEqx : index FZ (insertAt (FS k) x (y :: ys)) = index (FS k) (insertAt (FS k) x (y :: ys))
>       yEqx =
>         (index FZ (insertAt (FS k) x (y :: ys)))      ={ Refl }=
>         (index FZ (y :: (insertAt k x ys)))           ={ Refl }=
>         (y)                                           ={ sym xEqy }=
>         (x)                                           ={ sym (insertAtIndex (FS k) x (y :: ys)) }=
>         (index (FS k) (insertAt (FS k) x (y :: ys)))  QED
> insAppRepeats (FS k) x (y :: ys) ((FS i) ** xEqysi) 
>   with (insAppRepeats k x ys (i ** xEqysi))
>   | (j ** (l ** (jLTl, ysjEqysl))) = ((FS j) ** ((FS l) ** (LTEFSucc jLTl, ysjEqysl)))



> ||| If x appears in ys and y is inserted, x still appears in the result:
> |||
> insKeepsApp : {A : Type} -> {n : Nat} -> 
>               (k : Fin (S n)) -> (x, y : A) -> (ys : Vect n A) ->
>               Appears x ys -> Appears x (insertAt k y ys)
>
> insKeepsApp FZ      x y ys (i ** xEqysi) = ((FS i) ** xEqysi)
> insKeepsApp (FS k) x y Nil (FZ ** _) impossible
> insKeepsApp (FS k) x y (z :: ys) (FZ ** xEqz)  = (FZ ** xEqz)
> insKeepsApp (FS k) x y (z :: ys) ((FS j) ** xEqysj)
>     with (insKeepsApp k x y ys (j ** xEqysj))
>     | (l ** xEqyysl) = ((FS l) ** xEqyysl)



> ||| If ys has a repeat, ys with another element inserted still has a repeat
> |||
> insKeepsRep : {A : Type} -> {n : Nat} -> 
>               (k : Fin (S n)) -> (x : A) -> (ys : Vect n A) ->
>               Repeats ys -> Repeats (insertAt k x ys)
>
> insKeepsRep _ _ Nil (FZ ** (_ ** _)) impossible
> insKeepsRep _ _ _ (_ ** (FZ ** (LTEFZero, _))) impossible
> insKeepsRep _ _ _ (_ ** (FZ ** (LTEFSucc _, _))) impossible
>
> insKeepsRep FZ      x  ys   (i ** (j ** (iLTj, ysiEqysj))) = 
>     ((FS i) ** ((FS j) ** (LTEFSucc iLTj, ysiEqysj)))
>
> insKeepsRep (FS k) x (y :: ys) (FZ ** ((FS j) ** (fZLTj, yEqysj)))
>   with (insKeepsApp k y x ys (j ** yEqysj))
>   | (l ** yEqinsl) = (FZ ** ((FS l) ** (LTEFSucc LTEFZero, yEqinsl)))
>
> insKeepsRep (FS k) x (y :: ys) ((FS i) ** ((FS j) ** (LTEFSucc iLTj, ysiEqysj)))
>   with (insKeepsRep k x ys (i ** ( j ** (iLTj, ysiEqysj))))
>   | (l ** (m ** (lLTm, inslEqinsm))) = ((FS l) ** ((FS m) ** (LTEFSucc lLTm, inslEqinsm)))



> ||| Removes an appearing element from a vector, and along with the 
> ||| rest vector returns an index and a proof that inserting the 
> ||| removed element at that index into the rest vector gives back 
> ||| the original vector:
> |||
> removeAppearing : {A : Type} -> {n : Nat} -> 
>                   (x : A) -> (ys : Vect (S n) A) ->
>                   Appears x ys -> 
>                   ( ys' : Vect n A ** 
>                       ( k : Fin (S n) ** 
>                           (insertAt k x ys') = ys 
>                       )
>                   )
>
> removeAppearing x (y :: ys) (FZ ** xEqy) = 
>     ( ys ** ( FZ ** xysEqyys )) where
>       xysEqyys : (x :: ys) = (y :: ys)
>       xysEqyys = cong {f = \z => z :: ys} xEqy
>
> removeAppearing {n=Z} _ _ ((FS FZ) ** _) impossible
>
> removeAppearing {n=(S _)} x (y :: ys) ((FS j) ** xEqysj) 
>     with (removeAppearing x ys (j ** xEqysj)) 
>     | (ys' ** (k' ** prf'))  = 
>       ((y :: ys') ** ((FS k') ** prf)) where
>         prf : insertAt (FS k') x (y :: ys') = (y :: ys)
>         prf  = cong {f = \zs => y :: zs} prf'



> ||| If FZ does not appear in a vector xs over (Fin (S n)), 
> ||| xs is map FS xs' for some vector xs' over (Fin n):
> |||
> finVectFromBelow : {n, m : Nat} -> (xs : Vect m (Fin (S n))) -> 
>                    Not (Appears FZ xs) -> 
>                    (zs : (Vect m (Fin n)) ** map FS zs = xs)
>
> finVectFromBelow Nil            _          = (Nil ** Refl)
> finVectFromBelow ( FZ    :: xs) fzNotInxxs = 
>     void (fzNotInxxs (FZ ** Refl))
> finVectFromBelow ((FS z) :: xs) fzNotInxxs 
>     with (finVectFromBelow xs (notAppearsTail FZ (FS z) xs fzNotInxxs))
>     | (zs ** mapFSzsEqxs) = ((z :: zs) ** mapFSzzsEqxxs) where
>       mapFSzzsEqxxs  : map FS (z :: zs) = ((FS z) :: xs)
>       mapFSzzsEqxxs  = cong {f = \ys => (FS z) :: ys} mapFSzsEqxs


Finally:

> pigeonHole : {n, m : Nat} -> 
>              (n `LT` m) -> (xs : Vect m (Fin n)) -> 
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
>                     mapFSzs'Repeats : Repeats (map FS zs')
>                     mapFSzs'Repeats = functRepeats FS zs' zs'Repeats
>                     zsRepeats = replace {P = Repeats} mapFSzs'Eqzs (functRepeats FS zs' zs'Repeats)
>                     xsRepeats : Repeats xs
>                     xsRepeats = replace inskfzzsEqxs (insKeepsRep k FZ zs zsRepeats)
>        | (No  fzNotInxs) 
>           with (finVectFromBelow xs fzNotInxs) 
>           | (xs' ** mapFSxs'Eqxs) = void (xsNotRepeats xsRepeats) where
>               xs'Repeats : Repeats xs'
>               xs'Repeats = pigeonHole (lteSuccRight pLTq) xs'
>               xsRepeats : Repeats xs
>               xsRepeats = replace {P = Repeats} mapFSxs'Eqxs (functRepeats FS xs' xs'Repeats)


