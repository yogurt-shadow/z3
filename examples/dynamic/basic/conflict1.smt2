(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (>= y 23))
(assert (<= z 18))
(assert (or (< y (+ x 10)) (> z (+ x 30))))

(check-sat)
