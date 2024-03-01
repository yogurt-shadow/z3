(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-info :category "industrial")

(declare-fun V1 () Real)
(declare-fun V2 () Real)
(declare-fun V3 () Real)
(declare-fun V4 () Real)
(assert (and (<= 0 V1) (<= 0 V2) (<= 0 V3) (<= 1 V4) (<= 0 V4) (<= 0 (+ 1 V4)) (<= 0 (+ 2 V4)) (<= 0 (+ 3 V4)) (or (and (< 0 (+ 13 (* V4 2))) (<= 0 (+ (* V1 (+ 7 (* V4 2))) (* (* V2 (+ 20 (* V4 3))) (- 1)) (* V3 (+ 22 (* V4 5)))))) (and (< (* V4 2) (- 13)) (<= (+ (* V1 (+ 7 (* V4 2))) (* (* V2 (+ 20 (* V4 3))) (- 1)) (* V3 (+ 22 (* V4 5)))) 0))) (or (and (< 0 (* (+ 13 (* V4 2)) (+ 15 (* V4 2)))) (< (+ (* V1 (+ (* (* V4 V4) 10) (* V4 89) 189)) (* (* V2 (+ (* (* V4 V4) 11) (* V4 137) 423)) (- 1)) (* V3 (+ (* (* V4 V4) 19) (* V4 160) 295))) 0)) (and (< (* (+ 13 (* V4 2)) (+ 15 (* V4 2))) 0) (< 0 (+ (* V1 (+ (* (* V4 V4) 10) (* V4 89) 189)) (* (* V2 (+ (* (* V4 V4) 11) (* V4 137) 423)) (- 1)) (* V3 (+ (* (* V4 V4) 19) (* V4 160) 295))))))))
(check-sat)
(exit)



















