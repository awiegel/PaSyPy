(set-logic NRA)
(set-info :source | Produced by Alexander Wiegel |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(assert (not (= (* (- x 7.5) (* (- x 5) (* (- x 2.5) (* (+ x 2.5) (* (+ x 5) (* (+ x 7.5) x)))))) 0)))
(check-sat)
