(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

(assert (> (+ (* x x) x y (- 12)) 0))
(assert (or(> (+ (* x x) (* 3 x) y (- 16)) 0) (> (+ (* x x) (* 3 x) y (- 13)) 0) ))
(assert (> (+ (* x x) (- x) (- y) 14) 0))

(check-sat)
(get-model)