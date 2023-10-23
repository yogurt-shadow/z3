(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status unsat)
(set-info :category "industrial")

(declare-fun V1 () Real)
(declare-fun V2 () Real)
(assert (and (<= 1 V1) (<= 0 V1) (<= 0 (+ 1 V1)) (<= (+ (- 3) (* V1 4)) (* (* V2 V2) 4)) (or (and (< 0 (* V2 V2)) (<= (* (+ 1 (* V1 4)) (* V2 V2)) (* (* (+ V1 V2) (+ V1 V2)) 4))) (and (< (* V2 V2) 0) (<= (* (* (+ V1 V2) (+ V1 V2)) 4) (* (+ 1 (* V1 4)) (* V2 V2))))) (or (and (< 0 (* (+ V1 V2) (+ V1 V2))) (< (* (* (+ (* V2 2) (* V1 (+ 1 V2))) (+ (* V2 2) (* V1 (+ 1 V2)))) 4) (* (+ 5 (* V1 4)) (* (+ V1 V2) (+ V1 V2))))) (and (< (* (+ V1 V2) (+ V1 V2)) 0) (< (* (+ 5 (* V1 4)) (* (+ V1 V2) (+ V1 V2))) (* (* (+ (* V2 2) (* V1 (+ 1 V2))) (+ (* V2 2) (* V1 (+ 1 V2)))) 4))))))
(check-sat)
(exit)




















