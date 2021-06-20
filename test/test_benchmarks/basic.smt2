(set-logic NRA)
(set-info :source | Produced by tarski version 1.29  |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (exists ((z Real)) (and (>=  x 0.5) (>=  y 0.5) (> z x) (< z y))))
(check-sat)