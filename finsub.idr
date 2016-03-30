-- this is obsolete, see FinSub.lidr
module FinSub

import Data.Fin
import Syntax.PreorderReasoning

%default total

-- goal: formalize as much of automata theory as possible in idris
-- 
-- 1.subgoal: for alphabets, states etc we need the notion
-- of a finite subset of a type (e.g. of Char, String, ...)
-- should be able to
--   find the cardinality of such a finite set
--   show a list of all the elements if elements are showable

-- finite subset of a given type a are given 
-- by a cardinality card and an injective function (Fin card) -> a
--
-- injective functions:

data Injective : {a : Type} -> {b : Type} -> (f:(a -> b)) -> Type where
  isInj : {a : Type} -> {b : Type} -> {f:(a->b)} -> 
          ((x:a) -> (y:a) -> ((f x)=(f y)) -> 
          (x=y)) -> Injective f

-- Some properties of injective functions

----  identity functions are injective

idIsInj : {a:Type} -> Injective (id {a = a})
idIsInj = isInj p where
  p x x Refl = Refl

---- composition of injectives is injective

compInj : {a : Type} -> {b : Type} -> {c : Type} -> 
          {f : (a->b)} -> {g : (b->c)} -> 
          Injective f -> Injective g -> 
          Injective ((.) g f)

compInj {a = a} {f = f} {g = g} (isInj fInj) (isInj gInj) = isInj gfInj 
  where
    gfInj : (x:a) -> (y:a) -> (g . f) x = (g . f) y -> x = y
    gfInj x y = fInj x y . gInj (f x) (f y)


-- finite subsets:

data FinSub : (a:Type) -> Type where
  finSub : (card:Nat) -> (f:(Fin card)->a) -> (Injective f) -> FinSub a

-- we want to build up injections Fin n -> a inductively
---- base case: the embedding of the empty set (Fin Z)

emptyEmb : ((Fin Z)->a)
emptyEmb  FZ       impossible
emptyEmb  (FS _)   impossible

---- it is injective
emptyInj : {a:Type} -> Injective (emptyEmb {a = a})
emptyInj {a = a} = 
      isInj {a = Fin Z} {b = a} {f = emptyEmb} p where
          p : (x:(Fin Z)) -> (y:(Fin Z)) -> 
              (emptyEmb {a = a} x) = (emptyEmb {a = a} y) -> (x = y)
          p   FZ      _  _ impossible
          p   (FS _)  _  _ impossible

---- the empty set is a finite subset of every type
emptySub : {a:Type} -> FinSub a
emptySub {a = a} = finSub Z emptyEmb emptyInj

-- given an injection   f:(Fin n)->a, 
-- an element           x:a,
-- and a proof that x isn't equal to any f y, we can define
-- an injection mapping 0 |-> x and fS y |-> f y

extFinMap : (f: (Fin n) -> a) -> (x:a) -> (Fin (S n)-> a)
extFinMap f x  FZ       = x
extFinMap f x (FS x')   = f x' 

extInj : (f:(Fin n)->a) -> (x:a) 
        -> ( m:(Fin n) -> ((f m) = x) -> Void ) 
        -> Injective f -> Injective (extFinMap f x)

extInj {n = n} f x xnotinf fIsInj = isInj {f = (extFinMap f x)} eInj where
     eInj : (w:(Fin (S n))) -> (z:(Fin (S n))) -> ((extFinMap f x w) = (extFinMap f x z)) -> (w=z)
     eInj  FZ     FZ     _ = Refl
     eInj (FS m)  FZ     s = ?one -- void (xnotinf m s)
     eInj  FZ    (FS m)  s = ?two -- void (xnotinf m (sym s))
     eInj (FS m) (FS m') s with (fIsInj)
       eInj (FS m) (FS m') s | isInj fInj = cong ( fInj m m' s )

-- For an arbitrary type, it might be difficult to get hands on "a proof 
-- that x isn't equal to any f y" i.e. a proof that some x is not in the 
-- finite subset described by f
-- If a has decidable equality, we can decide whether some element belongs 
-- to the subset (by giving it's index) or not (giving a proof as above)... t.b.c.

-- ================================================================
-- 30.01.2015 neuer Ansatz

-- two elements in a Fin n are either equal or not equal, i.e. equality
-- in Fin n is decidable

eqDecFin : (x:(Fin n)) -> (y:(Fin n)) -> Either (x=y) (Not (x=y))
eqDecFin FZ      FZ       = Left Refl
eqDecFin (FS x') (FS y')  with (eqDecFin x' y')
  eqDecFin (FS x') (FS y') | Left  predEq    = Left (cong predEq)
  eqDecFin (FS x') (FS y') | Right predNotEq = Right ?notEq
eqDecFin FZ      (FS y')  = Right (\p => replace {P = disjointTy} p ()) where
  disjointTy : (Fin n) -> Type
  disjointTy FZ     = ()
  disjointTy (FS z) = Void
eqDecFin (FS y')   FZ     = Right (\p => replace {P = disjointTy} p ()) where
  disjointTy : (Fin n) -> Type
  disjointTy FZ     = Void
  disjointTy (FS z) = ()

