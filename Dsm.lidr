> module Dsm
>
> import Data.Fin
> import Syntax.PreorderReasoning
>
> %default total
> %access public export

We represent a deterministic state machine
as a coalgebra of the functor

  s |-> (a -> s, Bool)

where the type a represents an alphabet:
 
> DSM : Type -> Type -> Type
> DSM a s = s -> (a -> s, Bool)

Such a coalgebra is given by its components

  s -> a -> s    this is the transition function
  s -> Bool      this is the boolean predicate decscribing 
                 final (accepting) states

Note that a DSM has no start state.

We define the transition function and predicate of
accepting states of a DSM:

> transFun : {a, s : Type} -> DSM a s -> s -> a -> s
> transFun f = fst . f

> accStatePred : {a, s : Type} -> DSM a s -> s -> Bool
> accStatePred f = snd . f

and give a "smart constructor":

> dsm : {a, s : Type} -> (s -> a -> s) -> (s -> Bool) -> DSM a s
> dsm t f state = (t state, f state)

Given a dsm and a start state, we get a predicate on 
lists over a (i.e. a language over a)

> langDSM : {a, s : Type} -> DSM a s -> s -> List a -> Bool
> langDSM m state []      = (accStatePred m) state          
> langDSM m state (x::xs) = langDSM m (transFun m state x) xs

We define deterministic state machines with a start state:

> DSMS : Type -> Type -> Type
> DSMS a s = (DSM a s, s)

These now have "their" language

> langDSMS : {a, s : Type} -> DSMS a s -> List a -> Bool
> langDSMS (m, s) = langDSM m s

For convenience we also give a "smart constructor"

> dsms : {a, s : Type} -> 
>        (s -> a -> s) -> (s -> Bool) -> s -> DSMS a s
> dsms t f start = (dsm t f, start)

Configurations: A configuration of a DSM is the type of
pairs of states and lists over the alphabet. Since it
does neither depend on the transition function nor on
start or final states, we parametrize it only by a and s

> DSMConf : Type -> Type -> Type
> DSMConf a s = (s, List a)

A DSM determines a function

> nextConf : {a, s : Type} -> DSM a s -> DSMConf a s -> Maybe (DSMConf a s)
> nextConf ts (state, Nil)      = Nothing
> nextConf ts (state, (a::as))  = Just (transFun ts state a, as)

Given a DSM, a start state and an input string, we can
accumulate all configurations into a list:

> confSequence : {a, s : Type} -> DSM a s -> s -> List a -> List (DSMConf a s)
> confSequence ts state Nil     = (state, Nil) :: Nil
> confSequence ts state (a::as) = (state, (a::as)) :: confSequence ts (transFun ts state a) as


Here's the extended transition function

W need a helper function to convince idris of the 
totality of extTransFun

> extTransFun' : {a, s : Type} -> DSM a s -> s -> List a -> s
> extTransFun' f state []      = state
> extTransFun' f state (a::as) = extTransFun' f (transFun f state a) as

> extTransFun : {a, s : Type} -> DSM a s -> DSMConf a s -> s
> extTransFun f (state, as) = extTransFun' f state as

Using extTransFun, one can define langDSM alternatively as

> langDSM' : {a, s : Type} -> DSM a s -> s -> List a -> Bool
> langDSM' m state as = accStatePred m (extTransFun m (state, as))

This is indeed the same as langDSM

> langDSMLemma : {a, s : Type} -> 
>                (m : DSM a s) -> (state: s) -> (as : List a) ->
>                langDSM' m state as = langDSM m state as
> langDSMLemma m state []      = Refl
> langDSMLemma m state (a::as) = 
>   (langDSM' m state (a::as)) 
>   ={ Refl }=
>   (accStatePred m (extTransFun m (state, (a::as))))
>   ={ Refl }=
>   (accStatePred m (extTransFun m ((transFun m state a),as)))
>   ={ Refl }=
>   (langDSM' m (transFun m state a) as)
>   ={ langDSMLemma m (transFun m state a) as }=
>   (langDSM m (transFun m state a) as)
>   ={ Refl }=
>   (langDSM m state (a::as))
>   QED


Examples
--------

Here are some very basic machines that can be defined 
over any alphabet a

The machine that accepts nothing has one state (which
of cause has to be the start state), a trivial transition 
function and no final states:

> accNone : DSMS a (Fin 1)
> accNone = (f, FZ) where
>  f state = (const FZ, False)

By making the one and only state final, one gets the
machine that accepts anything:

> accAll : DSMS a (Fin 1)
> accAll = (f, FZ) where
>  f state = (const FZ, True)

To define a machine accepting the empty string, but nothing 
else, we already need two states

> accJustNil : DSMS a (Fin 2)
> accJustNil = (f, FZ) where
>  f FZ      = (const (FS FZ), True)
>  f (FS FZ) = (const (FS FZ), False)
>  f (FS (FS FZ)) impossible

Here is a function producing machines that accept
singletons.

> accJustOne : Eq a => a -> DSMS a (Fin 3)
> accJustOne x = (f, FZ) where
>  f FZ            = (f0 , False) where
>    f0 y = if (y == x) then (FS FZ) else (FS (FS FZ))
>  f (FS FZ)       = (const (FS (FS FZ)), True)
>  f (FS (FS FZ))  = (const (FS (FS FZ)), False)
>  f (FS (FS (FS FZ))) impossible


