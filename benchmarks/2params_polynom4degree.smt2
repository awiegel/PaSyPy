(set-logic NRA)
(set-info :source | Produced by Alexander Wiegel |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (<= (* 2 x) (+ (* y (* y (* y y))) 0.5)))
(check-sat)