(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

(assert (or (< (+ (* x x) (* 3 x) 2) y) (< (+ (* x x) (* 7 x) 12) y)))
(assert (or (< (+ (* x x) (* 11 x) 30) y) (< (+ (* x x) (* 15 x) 56) y)))

(check-sat)
(get-model)