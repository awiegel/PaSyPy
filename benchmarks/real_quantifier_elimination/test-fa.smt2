(set-logic QF_NRA)
(set-info :source | Produced by tarski version 1.29  |)
(set-info :smt-lib-version 2.0)
(declare-fun m () Real)
(declare-fun x () Real)
(assert  (exists ((x Real))  (<  (+ (+ (- 1) (* m m)) (* x x)) 0)))
(check-sat)
