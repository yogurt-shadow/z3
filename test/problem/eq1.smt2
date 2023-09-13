(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

(assert (= x (+ 1 (* 2 y))))
(assert (> y 0))
(assert (= (- (* x x) 1) 0))

(check-sat)
