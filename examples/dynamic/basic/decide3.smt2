(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (or (= (+ x y) 0) (= (- x y) 0)))
(assert (= (* x x) (- (* z z) 1)))

(check-sat)
