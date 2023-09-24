(set-logic QF_NRA)

(declare-const a Bool)
(declare-const y Real)
(declare-const x Real)

(assert (> y 24))
(assert (or a (< (+ (* x x) y) 12)))

(check-sat)
(get-model)
