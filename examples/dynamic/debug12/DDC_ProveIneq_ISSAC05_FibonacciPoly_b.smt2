(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status unsat)
(set-info :category "industrial")

(declare-fun V1 () Real)
(declare-fun V2 () Real)
(declare-fun V3 () Real)
(declare-fun x () Real)
(assert (and (or (and (< 0 (* (+ (* x x) 2) (+ (* x x) 2) (+ (* x x) 2))) (<= (* (* (+ (* x x) 2) (+ (* x x) 2) (+ (* x x) 2)) (* V1 V1)) (* (* (+ (* x x) 1) (+ (* x x) 1)) V3))) (and (< (* (+ (* x x) 2) (+ (* x x) 2) (+ (* x x) 2)) 0) (<= (* (* (+ (* x x) 1) (+ (* x x) 1)) V3) (* (* (+ (* x x) 2) (+ (* x x) 2) (+ (* x x) 2)) (* V1 V1))))) (or (and (< 0 (* (+ (* x x) 2) (+ (* x x) 2))) (<= (* (* (+ (* x x) 2) (+ (* x x) 2)) (* V2 V2)) (* (* (+ (* x x) 1) (+ (* x x) 1)) V3))) (and (< (* (+ (* x x) 2) (+ (* x x) 2)) 0) (<= (* (* (+ (* x x) 1) (+ (* x x) 1)) V3) (* (* (+ (* x x) 2) (+ (* x x) 2)) (* V2 V2))))) (or (and (< 0 (+ (* x x) 2)) (< (* (* (+ (* x x) 1) (+ (* x x) 1)) V3) (* (+ (* x x) 2) (* (+ (* x V2) V1) (+ (* x V2) V1))))) (and (< (* x x) (- 2)) (< (* (+ (* x x) 2) (* (+ (* x V2) V1) (+ (* x V2) V1))) (* (* (+ (* x x) 1) (+ (* x x) 1)) V3))))))
(check-sat)
(exit)





















