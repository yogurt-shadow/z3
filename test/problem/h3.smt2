(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

((assert (or (>= (* (+ x 1) y) 10) (>= (* (+ x 1) y) 6) (>= (* (+ x 1) y) 7) (>= (* (+ x 1) y) 8) (<= (* (+ x 1) y) 5)))
(assert (< (+ (* y y) (* -7 y) 12) 0)))

(check-sat)
(get-model)
