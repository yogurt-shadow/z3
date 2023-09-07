(set-logic QF_LRA)

(declare-const x Real)
(declare-const y Real)

(assert (< (* 4 y) (+ x 4)))
(assert (> (* 4 y) (+ x 2)))

(check-sat)
(get-model)
