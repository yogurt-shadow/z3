(set-logic QF_NRA)

(declare-const x Real)

(assert (or (< (+ (* x x) (* (- 3) x) 2) 0) (< (+ (* x x) (* (- 7) x) 12) 0)))
(assert (or (< (+ (* x x) (* 3 x) 2) 0) (< (+ (* x x) (* 7 x) 12) 0)))

(check-sat)
