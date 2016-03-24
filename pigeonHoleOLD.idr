module PigeonHole

import Data.Fin
import Data.Vect
import Control.Isomorphism
import Syntax.PreorderReasoning

%default total

imagesEqual : {m, n : Nat} ->
              (f : Fin m -> Fin n) ->
              (Fin m , Fin m) ->
              Type
imagesEqual f (x, y) = (Not (x = y), f x = f y)

pigeonHole : (m, n : Nat) -> 
             ((S n) `LTE` m) -> 
             (f : Fin m -> Fin n) ->
             Sigma (Fin m, Fin m) (imagesEqual f)

--
--    f : Fin (S m') -> Fin (S n')
--    p : n' `LT` m'
--
--    f . FS : Fin m' -> Fin (S n')
--
--    take (f FZ) "out" of Fin (S n'):
--      
--      toMaybe:  Fin (S n') <-> Maybe (Fin n')  :fromMaybe
--
--    here we have  fromMaybe Nothing = (f FZ)
--
--    now either 
--      1) induced mapping 
--         (f' :=) toMaybe . f . FS : Fin m' -> Maybe (Fin n')
--         maps something to Nothing, or 
--
--      2) f' ~ Just . f'' with
--         some mapping  f'' : Fin m' -> Fin n'
--
--      in case 1) we have x' : Fin m' with
--             (toMaybe . f . FS) x' = Nothing  =>
--            (fromMaybe . toMaybe . f . FS) x' = (f FZ)  =>
--            f (FS x') = f FZ
--        and obviously Not (FS x' = FZ).
--
--      in case 2) for f'' : Fin m' -> Fin n' there are by induction
--        x, y : Fin m' with (Not x = y) and f'' x = f'' y
--        
--        f' x = f' y  <=>
--        (toMaybe . f . FS) x' = (toMaybe . f . FS) y' =>
--         (apply fromMaybe and use (fromMaybe . toMaybe = id))
--        f (FS x') = f (FS y')
--        
--        by FSInjective => Not ((FS x') = (FS y'))  


Identifies : {A, B : Type} -> (x : A) -> (y : B) -> Iso A B -> Type
Identifies x y (MkIso to _ _ _) = to x = y

IsoIdentifying : {A, B : Type} -> (x : A) -> (y : B) -> Type
IsoIdentifying x y = Sigma (Iso A B) (Identifies x y)


-- different approach:
--   pointed types and pointedIsos:

data PType : Type where
  Point: (A : Type) -> (x : A) -> PType

PIso: PType -> PType -> Type
PIso (Point A x) (Point B y) = IsoIdentifying x y

pIsoRefl : {ax : PType} -> PIso ax ax
pIsoRefl {ax = (Point A x)} = (isoRefl ** Refl)

pIsoSym : {ax, by : PType} -> PIso ax by -> PIso by ax
pIsoSym {ax = (Point A x)} {by = (Point B y)} ((MkIso to from toFrom fromTo) ** toxIsy) = 
  ((MkIso from to fromTo toFrom) ** fromyIsx) where
    fromyIsx : from y = x
    fromyIsx =
      (from y)      ={ cong (sym toxIsy) }=
      (from (to x)) ={ fromTo x          }=
      x             QED

pIsoTrans : {ax, by, cz : PType} -> PIso ax by -> PIso by cz -> PIso ax cz
pIsoTrans {ax = Point A x} {by = Point B y} {cz = Point C z} 
  ((MkIso to1 from1 toFrom1 fromTo1) ** to1xIsy)
  ((MkIso to2 from2 toFrom2 fromTo2) ** to2yIsz) =
  ((isoTrans (MkIso to1 from1 toFrom1 fromTo1) (MkIso to2 from2 toFrom2 fromTo2)) ** pf) where
    pf : to2 (to1 x) = z
    pf = trans (cong to1xIsy) to2yIsz

-- it would be much nicer to write that as following,
--    but that doesn't work
--    ... COULD it work??
--pIsoTrans (phi1 ** to1xIsy) (phi2 ** to2yIsz) =
--   ((isoTrans phi1 phi2) ** (trans (cong to1xIsy) to2yIsz))

-- ok, and then we are at 'multipointed' types

-- some preparations first

toOf : Iso a b -> (a -> b)
toOf (MkIso to _ _ _) = to

-- mapId and mapComp in principle make Vect n an Instance of VerifiedFunctor

mapId : (as : Vect n a) -> Functor.map Prelude.Basics.id as = as
mapId Nil = Refl
mapId (a :: as) =
  (map id (a :: as))   ={ Refl }=
  (a :: map id as  )   ={ cong {f = \y => a :: y} (mapId as) }=
  (a :: as)             QED

mapComp : (f : b -> c) -> (g : a -> b) -> (as : Vect n a) ->
          (Functor.map (f . g) as) = Functor.map f (Functor.map g as)
mapComp f g Nil = Refl
mapComp f g (a :: as) =
    (map (f . g) (a :: as))        ={ Refl }=
    (f (g a) :: map (f . g) as)    ={ cong {f = \y => f (g a) :: y} (mapComp f g as) }=
    (f (g a) :: map f (map g as)) ={ Refl }=
    (map f ( g a :: (map g as)))  ={ Refl }=
    (map f ( map g (a :: as)))    QED

-- and here's one more we'll need: |map| maps homotopic maps to homotopic maps

mapHomotopy : (f, g : a -> b) -> ((x : a) -> f x = g x) -> (xs : Vect n a) -> Functor.map f xs = Functor.map g xs
mapHomotopy f g fHg Nil = Refl
mapHomotopy f g fHg (a :: as) = 
  (map f (a :: as)) ={ Refl }=
  (f a :: map f as) ={ cong {f = \y => y :: map f as} (fHg a) }=
  (g a :: map f as) ={ cong {f = \y => g a :: y} (mapHomotopy f g fHg as) }=
  (g a :: map g as) ={ Refl }=
  (map g (a :: as)) QED

-- mapFusion for Vect :

mapVFusion : (f : b -> c) -> (g : a -> b) -> (xs : Vect n a) ->
             map f (map g xs) = map (f . g) xs
mapVFusion f g Nil = Refl
mapVFusion f g (x :: xs) =
  (map f (map g (x :: xs)))        ={ Refl }=
  (map f (g x :: map g xs))        ={ Refl }=
  ((f . g) x :: map f (map g xs))  ={ cong {f = \y => (f . g) x :: y} (mapVFusion f g xs) }=
  ((f . g) x :: map (f . g) xs)    ={ Refl }=
  (map (f . g) (x :: xs))          QED

-- MPType n ... "n-pointed types"
-- isomorphic to ( A : Type ** Vect n A )

data MPType : (n : Nat) -> Type where
  MPoint  : (A : Type) -> Vect n A -> MPType n

baseType : MPType n -> Type
baseType (MPoint A _) = A

points : (axs : MPType n) -> Vect n (baseType axs)
points (MPoint _ xs) = xs

-- an isomorphism of n-pointed types is an isomorphism that
-- maps the distinguished points in the surce to those in the target

MPIso : {n : Nat} -> (MPType n) -> (MPType n) -> Type
MPIso (MPoint A as) (MPoint B bs) = (f : (Iso A B) ** Functor.map (toOf f) as = bs) 

-- projections

isoOf : MPIso axs bys -> Iso (baseType axs) (baseType bys)
isoOf {axs = MPoint A xs} {bys = MPoint B ys} (iso ** _) = iso

mapToPointsIsPointsOf : (iso : MPIso axs bys) ->
                   Functor.map (toOf (isoOf iso)) (points axs) =
                   points bys
mapToPointsIsPointsOf {axs = MPoint A xs} {bys = MPoint B ys}
                  (iso ** pf) = pf

-- MPIso is an equivalence relation on MPType n :

mpIsoRefl : {axs : MPType n} -> MPIso axs axs
mpIsoRefl {axs = (MPoint A xs)} = (isoRefl ** (mapIdIsId xs)) where
  mapIdIsId : (xs : Vect n a) -> Functor.map Prelude.Basics.id xs = xs
  mapIdIsId Nil = Refl
  mapIdIsId (x :: xs) = cong (mapIdIsId xs)

mpIsoSym : {axs, bys : MPType n} -> MPIso axs bys -> MPIso bys axs
mpIsoSym {axs = MPoint A xs} {bys = MPoint B ys} ((MkIso to from toFrom fromTo) ** toxsIsys) =
  ((MkIso from to fromTo toFrom) ** fromysIsxs) where
    fromysIsxs : Functor.map from ys = xs
    fromysIsxs = 
      (map from ys)          ={ cong (sym toxsIsys) }=
      (map from (map to xs)) ={ sym (mapComp from to xs)  }=
      (map (from . to) xs)   ={ mapHomotopy (from . to) id fromTo xs }=
      (map id xs)            ={ mapId xs }=         
      xs                      QED

mpIsoTrans : {axs, bys, czs : MPType n} -> MPIso axs bys -> MPIso bys czs -> MPIso axs czs
mpIsoTrans {axs = MPoint A xs} {bys= MPoint B ys} {czs = MPoint C zs} 
  ((MkIso to1 from1 toFrom1 fromTo1) ** to1xIsy)
  ((MkIso to2 from2 toFrom2 fromTo2) ** to2yIsz) =
  ((isoTrans (MkIso to1 from1 toFrom1 fromTo1) (MkIso to2 from2 toFrom2 fromTo2)) ** pf) where
    pf : Functor.map (to2 . to1) xs = zs
    pf = 
      (map (to2 . to1) xs)   ={ mapComp to2 to1 xs }=
      (map to2 (map to1 xs)) ={ cong to1xIsy       }=
      (map to2 ys)           ={ to2yIsz            }=
      zs                     QED


-- for any type A, MPoint A Nil is just A, and any iso 
-- can be considered a "0-pointed" iso

mpNilIso : Iso a b -> MPIso (MPoint a Nil) (MPoint b Nil)
mpNilIso iso = (iso ** Refl)

-- for any n-pointed type (MPoint A xs), 
-- we have a canonical (S n)-pointed type (MPoint (Maybe A) (Nothing :: map Just xs))

pointNothing : MPType n -> MPType (S n)
pointNothing (MPoint a xs) = MPoint (Maybe a) (Nothing :: map Just xs)

-- any MPIso axs bys induces an MPIso (pointNothing axs) (pointNothing bys)

pointNothingIso : {axs , bys : MPType n} ->
                  MPIso axs bys -> MPIso (pointNothing axs) (pointNothing bys)
pointNothingIso {axs = MPoint A xs} {bys = MPoint B ys} 
                ((MkIso to from toFrom fromTo) ** mapToXsIsYs) =
  ((MkIso to' from' toFrom' fromTo') ** prf) where
    to' : Maybe A -> Maybe B
    to' = Functor.map to
    from' : Maybe B -> Maybe A
    from' = Functor.map from
    toFrom' : (mb : Maybe B) -> to' (from' mb) = mb
    toFrom' Nothing  = Refl
    toFrom' (Just y) =
      (to' (from' (Just y)))  ={ Refl }=
      (Just (to (from y))  )  ={ cong (toFrom y) }=
      (Just y)                QED
    fromTo' : (ma : Maybe A) -> from' (to' ma) = ma
    fromTo' Nothing  = Refl
    fromTo' (Just x) =
      (from' (to' (Just x)))  ={ Refl }=
      (Just (from (to x))  )  ={ cong (fromTo x) }=
      (Just x)                QED
    prfJust : Functor.map to' (map Just xs) = map Just ys
    prfJust = 
      (map to' (map Just xs)) ={ mapVFusion to' Just xs }=
      (map (to' . Just) xs  ) ={ Refl }=
      (map (Just . to) xs   ) ={ sym (mapVFusion Just to xs) }=
      (map Just (map to xs) ) ={ cong mapToXsIsYs }=
      (map Just ys)           QED
    prf : Functor.map to' (Nothing :: map Just xs) = (Nothing :: map Just ys)
    prf =
      (map to' (Nothing :: map Just xs)) ={ Refl }=
      (Nothing :: map to' (map Just xs)) ={ cong {f = \y => Nothing :: y} prfJust }=
      (Nothing :: map Just ys)           QED

insertNothingAt : MPType n -> (i : Fin (S n)) -> MPType (S n)
insertNothingAt axs FZ = pointNothing axs
insertNothingAt {n = (S n')} axs i =
                (MPoint (Maybe (baseType axs)) 
                        (insertAt i Nothing (map Just (points axs))))

insertNothingIso : {axs , bys : MPType n} ->
                  (i : Fin (S n)) ->
                  MPIso axs bys -> 
                  MPIso (insertNothingAt axs i) (insertNothingAt bys i)
insertNothingIso {axs = MPoint A xs} {bys = MPoint B ys} 
                 i ((MkIso to from toFrom fromTo) ** mapToXsIsYs) =
  ((MkIso to' from' toFrom' fromTo') ** ?prf) where
    to' : Maybe A -> Maybe B
    to' = Functor.map to
    from' : Maybe B -> Maybe A
    from' = Functor.map from
    toFrom' : (mb : Maybe B) -> to' (from' mb) = mb
    toFrom' Nothing  = Refl
    toFrom' (Just y) =
      (to' (from' (Just y)))  ={ Refl }=
      (Just (to (from y))  )  ={ cong (toFrom y) }=
      (Just y)                QED
    fromTo' : (ma : Maybe A) -> from' (to' ma) = ma
    fromTo' Nothing  = Refl
    fromTo' (Just x) =
      (from' (to' (Just x)))  ={ Refl }=
      (Just (from (to x))  )  ={ cong (fromTo x) }=
      (Just x)                QED
    prfJust : Functor.map to' (map Just xs) = map Just ys
    prfJust = 
      (map to' (map Just xs)) ={ mapVFusion to' Just xs }=
      (map (to' . Just) xs  ) ={ Refl }=
      (map (Just . to) xs   ) ={ sym (mapVFusion Just to xs) }=
      (map Just (map to xs) ) ={ cong mapToXsIsYs }=
      (map Just ys)           QED
    prf0 : Functor.map to' (Nothing :: map Just xs) = (Nothing :: map Just ys)
    prf0 =
      (map to' (Nothing :: map Just xs)) ={ Refl }=
      (Nothing :: map to' (map Just xs)) ={ cong {f = \y => Nothing :: y} prfJust }=
      (Nothing :: map Just ys)           QED
--    prf : (j : Fin (S n)) -> Functor.map to'  (insertAt j Nothing xs) = 
--                                              (insertAt j Nothing ys)
--    prf FZ      = prf0
--    prf (FS j') 
--      (insertAt (FS j') Nothing (xs)


-- there is an automorphism of any (Maybe (Maybe a)) interchanging
-- Nothing and Just Nothing (and acting like the identity on (Just (Just x))

switchMaybeMaybe : {A : Type} -> 
                   MPIso (MPoint (Maybe (Maybe A))  [Nothing, Just Nothing]) 
                         (MPoint (Maybe (Maybe A))  [Just Nothing, Nothing])
switchMaybeMaybe {A} = 
  ((MkIso to to toTo toTo) ** Refl) where
  to : Maybe (Maybe A) -> Maybe (Maybe A)
  to Nothing          = Just Nothing
  to (Just Nothing)   = Nothing
  to (Just (Just x')) = Just (Just x')
  toTo : (x : Maybe (Maybe A)) -> to (to x) = x
  toTo Nothing          = Refl
  toTo (Just Nothing)   = Refl
  toTo (Just (Just x')) = Refl

-- in an MPIso with a nonempty list of points, we can pick any index
-- and get an MPIso of 1-pointed types
-- proof is particularly ugly...

indexMPIso : {n : Nat} -> {axs, bys : MPType (S n)} ->
            (MPIso axs bys) -> (i : Fin (S n)) -> 
            MPIso (MPoint (baseType axs) [index i (points axs)])
                  (MPoint (baseType bys) [index i (points bys)])
indexMPIso  {axs = MPoint A xs} {bys = MPoint B ys} 
            ((MkIso to from toFrom fromTo) ** mapToXsIsYs) i =
  ((MkIso to from toFrom fromTo) ** toXiIsYi) where
    toXiIsYi : Functor.map to (Data.Vect.(::) (index i xs) Nil) = 
               Data.Vect.(::) (index i ys) Nil
    toXiIsYi = sym yiIsToXi where
      indexMapF: (f : a -> b) -> (i : Fin n) -> (ys : Vect n a) ->
          Data.Vect.index i (Functor.map f ys) = f (Data.Vect.index i ys)
      indexMapF f FZ      (y :: ys) = Refl
      indexMapF f (FS i') (y :: ys) = indexMapF f i' ys
      yiIsToXi : Data.Vect.(::) (Data.Vect.index i ys) Nil = 
                 Functor.map to (Data.Vect.(::) (Data.Vect.index i xs) Nil)
      yiIsToXi = 
        [index i ys]          ={ cong {f = \x => [index i x]} (sym mapToXsIsYs)   }=
        [index i (map to xs)] ={ cong {f = \x => [x]} (indexMapF to i xs) }=
        [to ( index i xs)]    ={ Refl }=
        (map to [index i xs]) QED


separate : {n : Nat} -> (x : Fin (S n)) -> 
           MPIso (MPoint (Fin (S n)) [x]) (MPoint (Maybe (Fin n)) [Nothing])
separate {n=Z}      (FS FZ)     impossible
separate {n=Z}      (FS (FS _)) impossible
separate FZ = (maybeIsoS ** Refl) 
{--  
  ((MkIso to from toFrom fromTo) ** pfToxIsNothing) where
  to : Fin (S n) -> Maybe (Fin n)
  to FZ      = Nothing
  to (FS x') = Just x'
  from : Maybe (Fin n) -> Fin (S n)
  from Nothing  = FZ
  from (Just x') = FS x'
  toFrom : (y : Maybe (Fin n)) -> to (from y) = y
  toFrom Nothing = Refl
  toFrom (Just x') = Refl
  fromTo : (x : Fin (S n)) -> from (to x) = x
  fromTo FZ = Refl
  fromTo (FS x') = Refl
  pfToxIsNothing : Functor.map to [FZ] = Data.Vect.(::) Nothing Nil
  pfToxIsNothing = Refl
  --}
separate {n = (S n')} (FS x) = indexMPIso iso (FS FZ) where
  iso : MPIso (MPoint (Fin (S (S n')))     [FZ     , FS x   ]) 
              (MPoint (Maybe (Fin (S n'))) [Just FZ, Nothing])
{--
  iso =
    (MPoint (Fin (S (S n'))) [FZ, FS x])
    ={ maybeIsoS ** Refl }=
    (MPoint (Maybe (Fin (S n'))) [Nothing, Just x])
    ={ pointNothingIso (separate x) }=
    (MPoint (Maybe (Maybe (Fin n'))) [Nothing, Just Nothing])
    ={ switchMaybeMaybe }=
    (MPoint (Maybe (Maybe (Fin n'))) [Just Nothing, Nothing])
--}

--  Fin (S n') -> Maybe (Fin n')   [FZ, FS x] |-> [Nothing, Just x] 


-- maps from Fin n into Maybe A either map an element to Nothing
-- or they factor over Just, i.e. can be written as (Just . g) for 
-- some g : Fin n -> A

mapsFinToMaybeDicho : 
  {n : Nat} -> {A : Type} ->
  (f : Fin n -> Maybe A ) ->
  Either (x : (Fin n) ** (f x = Nothing))
         (g : ((Fin n) -> A) ** ((y : Fin n) -> f y = Just (g y) ))

mapsFinToMaybeDicho {A} {n=Z} f = 
  Right (absurd . FinZAbsurd ** (\y => absurd (FinZAbsurd y)))
mapsFinToMaybeDicho {A} {n=(S n')} f 
  with (f FZ) proof patternIsfFZ
  | Nothing = Left (FZ ** sym patternIsfFZ)
  | (Just z)  
    with (mapsFinToMaybeDicho {n = n'} (f . FS))
    | (Left  (x ** fFSxIsNothing)) = Left ((FS x) ** fFSxIsNothing)
    | (Right (g' ** fFSIsJustg'))  = Right (g ** fIsJustg) where
      g : (Fin (S n')) -> A
      g FZ = z
      g (FS y') = g' y'
      fIsJustg : (y : (Fin (S n'))) -> f y = Just (g y)
      fIsJustg FZ = sym patternIsfFZ
      fIsJustg (FS y') = fFSIsJustg' y'


pigeonHole m n LTEZero _ impossible
pigeonHole Z n (LTESucc p) _ impossible
pigeonHole (S m') Z (LTESucc _) f = absurd (f FZ)
pigeonHole (S m') (S n') (LTESucc p) f = lili where
    hIso : MPIso (MPoint (Fin (S n')) [f FZ]) 
                 (MPoint (Maybe (Fin n')) [Nothing])
    hIso = separate (f FZ) 
    h : Fin (S n') -> Maybe (Fin n')
    h = toOf (isoOf hIso)
    lili with (mapsFinToMaybeDicho h)
      | Left ( x ** hxIsNothing) = ?lala
      | Right ( g ** fyIsJustgy ) = ?lulu
 


