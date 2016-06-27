> module Dsm
>
> import Data.Fin
> import Syntax.PreorderReasoning
>
> %default total
> %access public export
> %auto_implicits off

We represent a deterministic state machine
as a coalgebra of the functor

  s |-> (a -> s, Bool)

where the type a represents an alphabet:
 
> DSM : Type -> Type -> Type
> DSM a s = s -> (a -> s, Bool)

Such a coalgebra is given by its components

  s -> a -> s    this is the transition function
  s -> Bool      this is the boolean predicate describing 
                 final (accepting) states

Note that a start state is not part of our definition of a
deterministic state machine.

We define the transition function and predicate of
accepting states of a DSM:

> transFun : {a, s : Type} -> DSM a s -> s -> a -> s
> transFun f = fst . f

> accStatePred : {a, s : Type} -> DSM a s -> s -> Bool
> accStatePred f = snd . f

and define a "smart constructor":

> dsm : {a, s : Type} -> (s -> a -> s) -> (s -> Bool) -> DSM a s
> dsm t f state = (t state, f state)

Given a dsm and a state, we get a boolean predicate on 
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

For convenience we also give a smart constructor

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

We need a helper function to convince idris of the 
totality of extTransFun

> extTransFun' : {a, s : Type} -> DSM a s -> s -> List a -> s
> extTransFun' f state []      = state
> extTransFun' f state (a::as) = extTransFun' f (transFun f state a) as

> extTransFun : {a, s : Type} -> DSM a s -> DSMConf a s -> s
> extTransFun f (state, as) = extTransFun' f state as

Using extTransFun, one can define langDSM alternatively as

> langDSM2 : {a, s : Type} -> DSM a s -> s -> List a -> Bool
> langDSM2 m state as = accStatePred m (extTransFun m (state, as))

This is indeed the same as langDSM

> langDSMLemma : {a, s : Type} -> 
>                (m : DSM a s) -> (state: s) -> (as : List a) ->
>                langDSM2 m state as = langDSM m state as
> langDSMLemma m state []      = Refl
> langDSMLemma m state (a::as) = 
>   (langDSM2 m state (a::as)) 
>   ={ Refl }=
>   (accStatePred m (extTransFun m (state, (a::as))))
>   ={ Refl }=
>   (accStatePred m (extTransFun m ((transFun m state a),as)))
>   ={ Refl }=
>   (langDSM2 m (transFun m state a) as)
>   ={ langDSMLemma m (transFun m state a) as }=
>   (langDSM m (transFun m state a) as)
>   ={ Refl }=
>   (langDSM m state (a::as))
>   QED

We define the onestep configuration transition relation
of a DSM

> data OnestepConfTransRel : 
>   {a, s : Type} ->
>   DSM a s ->
>   DSMConf a s ->
>   DSMConf a s ->
>   Type where
>   Step : 
>     {a, s : Type} ->
>     (dsm : DSM a s) ->
>     (q, p : s) ->
>     (x : a) ->
>     (xs : List a) ->
>     (transFun dsm q x = p) ->
>     OnestepConfTransRel dsm (q, x::xs) (p, xs)

and the configuration transition relation as its
symmetric transitive closure

> data ConfTransRel :
>   {a, s : Type} ->
>   DSM a s ->
>   DSMConf a s ->
>   DSMConf a s ->
>   Type where
>   ReflConfTransRel : 
>     {a, s : Type} ->
>     (dsm : DSM a s) ->
>     (k : DSMConf a s) ->
>     ConfTransRel dsm k k
>   StepConfTransRel :
>     {a, s : Type} ->
>     (dsm : DSM a s) ->
>     (k, l, m : DSMConf a s) ->
>     OnestepConfTransRel dsm k l ->
>     ConfTransRel dsm l m ->
>     ConfTransRel dsm k m

With that we have a third way to associate a predicate (i.e. a language) 
with a DSM and a state. This time, however, we define it as a Type-valued 
rather than Bool-valued function on (List a):

> langDSM3 : {a, s : Type} -> DSM a s -> s -> List a -> Type
> langDSM3 dsm state xs = 
>   (p : s ** (accStatePred dsm p = True, ConfTransRel dsm (state, xs) (p, Nil)))

For any dsm and state, langDSM3 dsm state describes the same language as
langDSM dsm state (and langDSM2 dsm state), in this sense:

langDSM3 dsm state xs is inhabited    iff    langDSM dsm state xs = True

We prove this by defining functions

> langDSM3LemmaTo :
>   {a, s : Type} ->
>   (dsm : DSM a s) ->
>   (state : s) ->
>   (word : List a) ->
>   langDSM3 dsm state word ->
>   (langDSM dsm state word = True)
>
> langDSM3LemmaTo dsm state _  
>   (_ ** (stateIsAcc, ReflConfTransRel _ _)) = stateIsAcc
>
> langDSM3LemmaTo dsm state Nil 
>   (_ ** (_, StepConfTransRel _ _ _ _ (Step _ _ _ _ _ _) _)) impossible
>
> langDSM3LemmaTo dsm state (x::xs) 
>   (p ** (pIsAcc, StepConfTransRel dsm _ _ _ (Step dsm _ q _ _ prf1) prf2)) =
>   replace {P = \s => langDSM dsm s xs = True} (sym prf1) prf where
>     prf : langDSM dsm q xs = True
>     prf = langDSM3LemmaTo dsm q xs (p ** (pIsAcc, prf2))

> langDSM3LemmaFrom :
>   {a, s : Type} ->
>   (dsm : DSM a s) ->
>   (state : s) ->
>   (word : List a) ->
>   (langDSM dsm state word = True) ->
>   langDSM3 dsm state word
>
> langDSM3LemmaFrom dsm state Nil stateIsAcc =
>   (state ** (stateIsAcc, ReflConfTransRel dsm (state,[])))
>
> langDSM3LemmaFrom {a} {s} dsm state (x::xs) isAcc 
>   with (langDSM3LemmaFrom dsm (transFun dsm state x) xs isAcc) 
>   | (p ** (pIsAcc, prf)) = 
>     (p ** (pIsAcc, StepConfTransRel dsm k l (p,[]) (Step dsm state q x xs Refl) prf)) 
>     where
>       q : s
>       q = transFun dsm state x
>       k : DSMConf a s
>       k = (state, (x::xs))
>       l : DSMConf a s
>       l = (q, xs)


To test yet another variant we define the configuration
transition relation as a boolean relation on configurations

Of course we now need decidable equalities on a and s

First onestep

> using (a: Type, s: Type)
> 
>   onestepConfTransRel : 
>     (Eq a, Eq s) =>
>     DSM a s ->
>     DSMConf a s ->
>     DSMConf a s ->
>     Bool
>   onestepConfTransRel dsm (q, Nil) _ = False
>   onestepConfTransRel dsm (q, x::xs) (p, ys) = (transFun dsm q x) == p && xs == ys

and the full configuration transition relation

> -- Helper function needed to satisfy the totatlity checker
>   ctrHelper :
>     (Eq a, Eq s) =>
>     DSM a s ->
>     s ->
>     List a ->
>     s ->
>     List a ->
>     Bool
>   ctrHelper dsm q Nil     p Nil     = q == p
>   ctrHelper dsm q Nil     p (y::ys) = False
>   ctrHelper dsm q (x::xs) p  ys     = onestepConfTransRel dsm (q, x::xs) (p, ys) ||
>                                         ctrHelper dsm (transFun dsm q x) xs p ys 
>   confTransRel :
>     (Eq a, Eq s) =>
>     DSM a s ->
>     DSMConf a s ->
>     DSMConf a s ->
>     Bool
>   confTransRel dsm (q, xs) (p, ys) = ctrHelper dsm q xs p ys


Examples
--------

Here are some very basic machines that can be defined 
over any alphabet a

The machine that accepts nothing has one state (which
of cause has to be the start state), a trivial transition 
function and no final states:

> accNone : {a : Type} -> DSMS a (Fin 1)
> accNone = (f, FZ) where
>  f state = (const FZ, False)

By making the one and only state final, one gets the
machine that accepts anything:

> accAll : {a : Type} -> DSMS a (Fin 1)
> accAll = (f, FZ) where
>  f state = (const FZ, True)

To define a machine accepting the empty string, but nothing 
else, we already need two states

> accJustNil : {a : Type} -> DSMS a (Fin 2)
> accJustNil = (f, FZ) where
>  f FZ      = (const (FS FZ), True)
>  f (FS FZ) = (const (FS FZ), False)
>  f (FS (FS FZ)) impossible

Here is a function producing machines that accept
singletons.

> accJustOne : {a : Type} -> Eq a => a -> DSMS a (Fin 3)
> accJustOne x = (f, FZ) where
>  f FZ            = (f0 , False) where
>    f0 y = if (y == x) then (FS FZ) else (FS (FS FZ))
>  f (FS FZ)       = (const (FS (FS FZ)), True)
>  f (FS (FS FZ))  = (const (FS (FS FZ)), False)
>  f (FS (FS (FS FZ))) impossible


