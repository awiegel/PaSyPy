(set-logic QF_NRA)
(set-info :source | Produced by Alexander Wiegel |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (exists ((z Real)) (and (>= x z) (>= z y))))
(check-sat)
