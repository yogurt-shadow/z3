(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

(assert (>= x y))
(assert (<= x y))
(assert (= (+ (* x x) (* y y)) 8))

(check-sat)
(get-model)