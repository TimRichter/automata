> module DFAExamples
>
> import Syntax.PreorderReasoning
> import Control.Isomorphism
> import Dsm
>
> %default total
> %auto_implicits off
> %access public export

We implement "by hand" some example automata
from the lecture

----------------------------------------------------------
1. toggle switch (Wechselschalter)
----------------------------------------------------------

the alphabet type will just have one symbol, namely "Press"

> data TSSymbol : Type where
>   Press : TSSymbol

the states will be "On" and "Off"

> data TSState : Type where
>   On  : TSState
>   Off : TSState

here's the simple transition function:
any press switches the state

> tsTrans : TSState -> TSSymbol -> TSState
> tsTrans On  Press = Off
> tsTrans Off Press = On

"On" is the only final state

> tsFinal : TSState -> Bool
> tsFinal Off = False
> tsFinal On  = True

and we start in the "Off" state

> tsStart : TSState
> tsStart = Off

We can now define the machine

> tss : DSMS TSSymbol TSState
> tss = dsms tsTrans tsFinal tsStart

And here it is without the start state (to have 
extTransFun a.s.o.):

> ts : DSM TSSymbol TSState
> ts = fst tss


prove that the language of ts are just the Lists of
odd length

define odd as a boolean predicate on Nat

> odd : Nat -> Bool
> odd    Z  = False
> odd (S n) = not (odd n)

and for convenience, let's also define "even"

> even : Nat -> Bool
> even = not . odd

we prove that the languages accepted when starting
in "Off" resp. "On" are the lists of odd resp. even lengths:

> tsLanguages : (ps : List TSSymbol) -> 
>   Pair (langDSM ts Off ps = odd (length ps))
>        (langDSM ts On  ps = even (length ps))
> tsLanguages Nil = (Refl, Refl)
> tsLanguages (Press::ps) 
>   with (tsLanguages ps)
>   | (pf1, pf2) = (pf2, trans pf1 (bEqNotNotb (odd (length ps)))) where
>     bEqNotNotb : (b : Bool) -> b = not (not b)
>     bEqNotNotb True  = Refl
>     bEqNotNotb False = Refl

> tssLanguage : (ps : List TSSymbol) -> 
>               (langDSMS tss ps) = (odd (length ps))
> tssLanguage ps = fst (tsLanguages ps)


------------------------------------------------------
2. TI1 accepts any list of characters that contains 
   ['T','I','1']
------------------------------------------------------

> data TI1States : Type where
>   Start : TI1States
>   T     : TI1States
>   TI    : TI1States
>   TI1   : TI1States

> ti1Trans : TI1States -> Char -> TI1States
> ti1Trans Start 'T' = T
> ti1Trans Start  _  = Start
> ti1Trans T     'T' = T
> ti1Trans T     'I' = TI
> ti1Trans T      _  = Start
> ti1Trans TI    'T' = T
> ti1Trans TI    '1' = TI1
> ti1Trans TI     _  = Start
> ti1Trans TI1    _  = TI1

> ti1Final : TI1States -> Bool
> ti1Final TI1 = True
> ti1Final _   = False

> ti1s : DSMS Char TI1States
> ti1s = dsms ti1Trans ti1Final Start

> ti1 : DSM Char TI1States
> ti1 = fst ti1s

for convenient testing we port the language predicate
to String

 ti1Lang : String -> Bool
 ti1Lang as = (langDSMS ti1) (unpack as)











