(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-info :category "industrial")

(declare-fun V1 () Real)
(declare-fun V2 () Real)
(declare-fun V3 () Real)
(assert (and (<= 0 V1) (<= 0 V2) (<= 1 V3) (<= 0 V3) (<= 0 (+ 1 V3)) (<= 0 (+ 2 V3)) (<= 0 (+ 3 V3)) (<= 0 (+ 4 V3)) (<= 0 (+ 5 V3)) (<= 0 (+ 6 V3)) (<= 0 (+ 7 V3)) (<= 0 (+ 8 V3)) (or (and (< 0 (* (* (+ 3 V3) (+ 3 V3)) 2)) (<= 0 (+ (* (* V1 (+ (* V3 V3) (* V3 5) 4)) (- 1)) (* V2 (+ (* (* V3 V3) 3) (* V3 17) 22))))) (and (< (* (* (+ 3 V3) (+ 3 V3)) 2) 0) (<= (+ (* (* V1 (+ (* V3 V3) (* V3 5) 4)) (- 1)) (* V2 (+ (* (* V3 V3) 3) (* V3 17) 22))) 0))) (or (and (< 0 (* (* (+ 3 V3) (+ 4 V3)) 4)) (<= 0 (+ (* (* V1 (+ (* (* V3 V3) 3) (* V3 17) 14)) (- 1)) (* V2 (+ (* (* V3 V3) 7) (* V3 45) 62))))) (and (< (* (* (+ 3 V3) (+ 4 V3)) 4) 0) (<= (+ (* (* V1 (+ (* (* V3 V3) 3) (* V3 17) 14)) (- 1)) (* V2 (+ (* (* V3 V3) 7) (* V3 45) 62))) 0))) (or (and (< 0 (* (* (+ 3 V3) (+ 5 V3)) 8)) (<= 0 (+ (* (* V1 (+ (* (* V3 V3) 7) (* V3 45) 38)) (- 1)) (* V2 (+ (* (* V3 V3) 15) (* V3 109) 158))))) (and (< (* (* (+ 3 V3) (+ 5 V3)) 8) 0) (<= (+ (* (* V1 (+ (* (* V3 V3) 7) (* V3 45) 38)) (- 1)) (* V2 (+ (* (* V3 V3) 15) (* V3 109) 158))) 0))) (or (and (< 0 (* (* (+ 3 V3) (+ 6 V3)) 16)) (<= 0 (+ (* (* V1 (+ (* (* V3 V3) 15) (* V3 109) 94)) (- 1)) (* V2 (+ (* (* V3 V3) 31) (* V3 253) 382))))) (and (< (* (* (+ 3 V3) (+ 6 V3)) 16) 0) (<= (+ (* (* V1 (+ (* (* V3 V3) 15) (* V3 109) 94)) (- 1)) (* V2 (+ (* (* V3 V3) 31) (* V3 253) 382))) 0))) (or (and (< 0 (* (* (+ 3 V3) (+ 7 V3)) 32)) (<= 0 (- (* (* V2 (+ (* (* V3 V3) 21) (* V3 191) 298)) 3) (* V1 (+ (* (* V3 V3) 31) (* V3 253) 222))))) (and (< (* (* (+ 3 V3) (+ 7 V3)) 32) 0) (<= (- (* (* V2 (+ (* (* V3 V3) 21) (* V3 191) 298)) 3) (* V1 (+ (* (* V3 V3) 31) (* V3 253) 222))) 0))) (or (and (< 0 (* (* (+ 3 V3) (+ 8 V3)) 64)) (<= 0 (+ (* (* V1 (+ (* (* V3 V3) 21) (* V3 191) 170)) (- 3)) (* V2 (+ (* (* V3 V3) 127) (* V3 1277) 2046))))) (and (< (* (* (+ 3 V3) (+ 8 V3)) 64) 0) (<= (+ (* (* V1 (+ (* (* V3 V3) 21) (* V3 191) 170)) (- 3)) (* V2 (+ (* (* V3 V3) 127) (* V3 1277) 2046))) 0))) (or (and (< 0 (* (* (+ 3 V3) (+ 9 V3)) 128)) (<= 0 (+ (* (* V1 (+ (* (* V3 V3) 127) (* V3 1277) 1150)) (- 1)) (* V2 (+ (* (* V3 V3) 255) (* V3 2813) 4606))))) (and (< (* (* (+ 3 V3) (+ 9 V3)) 128) 0) (<= (+ (* (* V1 (+ (* (* V3 V3) 127) (* V3 1277) 1150)) (- 1)) (* V2 (+ (* (* V3 V3) 255) (* V3 2813) 4606))) 0))) (or (and (< 0 (* (* (+ 3 V3) (+ 10 V3)) 256)) (< (+ (* (* V1 (+ (* (* V3 V3) 255) (* V3 2813) 2558)) (- 1)) (* V2 (+ (* (* V3 V3) 511) (* V3 6141) 10238))) 0)) (and (< (* (* (+ 3 V3) (+ 10 V3)) 256) 0) (< 0 (+ (* (* V1 (+ (* (* V3 V3) 255) (* V3 2813) 2558)) (- 1)) (* V2 (+ (* (* V3 V3) 511) (* V3 6141) 10238))))))))
(check-sat)
(exit)

























