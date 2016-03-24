import Unique

-- wanna show that "belonging to the fiber of f over y" is a proposition

inFiberIsUnique : (f:a->b) -> 
                  (y:b) ->
                  Unique1 {t0 = a} (\ x => f x = y)

inFiberIsUnique {a} {b} f y x = uip {a = b} {x = (f x)} {y}

