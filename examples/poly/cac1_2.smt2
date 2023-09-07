(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

(assert (< (* 4 y) (- (* x x) 4)))
(assert (> (* 4 y) (+ x 2)))
(assert (> (* 4 y) (- 4 (* (- x 1) (- x 1))) ))

(check-sat)
(get-model)
