(set-logic NRA)
(set-info :source | Produced by Alexander Wiegel |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and (>= x 0.2) (<= y 0.875) (>= x y)))
(check-sat)
