(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)

(assert (<= (+ (* x x) (* (- 7) x) 12) 0))
(assert (or (<= (* y y) (- x 5)) (<= (* y y) (- (* x x) 20))))

(check-sat)
