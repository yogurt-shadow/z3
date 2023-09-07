(set-logic QF_NRA)

(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)

(assert (< (+ (* x1 x1) (* x1 x3)) 10))
(assert (< (+ (* x2 x2) (* x2 x3)) 12))
(assert (< (+ (* x4 x4) (* x4 x3) x3) 8))

(assert (> x3 12))
(check-sat)
(get-model)