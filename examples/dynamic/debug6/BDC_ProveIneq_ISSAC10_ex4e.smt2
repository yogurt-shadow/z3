(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-info :category "industrial")

(declare-fun V1 () Real)
(declare-fun V2 () Real)
(declare-fun V3 () Real)
(assert (and (<= 0 V1) (<= 0 V2) (<= 1 V3) (<= 0 V3) (<= 0 (+ 1 V3)) (<= 0 (+ 2 V3)) (<= 0 (+ 3 V3)) (<= 0 (+ 4 V3)) (<= 0 (* (* (* (+ 3 V3) (+ 3 V3)) (- (* V1 (+ (* V3 V3) (* V3 5) 4)) (* V2 (+ (* (* V3 V3) 3) (* V3 17) 22)))) (- 2))) (<= 0 (* (* (+ 3 V3) (+ 4 V3) (+ (* (* V1 (+ (* (* V3 V3) 3) (* V3 17) 14)) (- 1)) (* V2 (+ (* (* V3 V3) 7) (* V3 45) 62)))) 4)) (<= 0 (* (* (+ 3 V3) (+ 5 V3) (+ (* (* V1 (+ (* (* V3 V3) 7) (* V3 45) 38)) (- 1)) (* V2 (+ (* (* V3 V3) 15) (* V3 109) 158)))) 8)) (< (* (* (+ 3 V3) (+ 6 V3) (+ (* (* V1 (+ (* (* V3 V3) 15) (* V3 109) 94)) (- 1)) (* V2 (+ (* (* V3 V3) 31) (* V3 253) 382)))) 16) 0) (not (= (* (* (+ 3 V3) (+ 3 V3)) 2) 0)) (not (= (* (* (+ 3 V3) (+ 4 V3)) 4) 0)) (not (= (* (* (+ 3 V3) (+ 5 V3)) 8) 0)) (not (= (* (* (+ 3 V3) (+ 6 V3)) 16) 0))))
(check-sat)
(exit)


























