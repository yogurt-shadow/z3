(set-logic QF_NRA)

(declare-const y Real)

(assert (or (< (+ (* y y) (* 7 y) 12) 0) (< (+ (* y y) (* -3 y) 2) 0) (< (+ (* y y) (* -11 y) 30) 0)))
(assert (> y 100))

(check-sat)
