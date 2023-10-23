(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (> z 10))
(assert (or (< z (+ (* x x) 5)) (< z (+ (* y y) 8))))

(check-sat)
(get-model)