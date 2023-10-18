(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (> z 1))
(assert (< z 10))
(assert (or (< (+ (* x x) 20) z) (< z (- (* y y) 10))))

(check-sat)
(get-model)