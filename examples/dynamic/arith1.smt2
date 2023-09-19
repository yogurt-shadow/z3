(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (> (- (* x x) (* y y)) 0))
(assert (> (+ (* x x) (* x z)) 10))

(check-sat)
(get-model)
