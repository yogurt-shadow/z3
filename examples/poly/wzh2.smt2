(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (>= (+ (* x x) (* x y)) 10))
(assert (<= (+ (* y y) (* y z)) 12))
(assert (<= (+ (* z z) (* x z)) 8))

(check-sat)
(get-model)