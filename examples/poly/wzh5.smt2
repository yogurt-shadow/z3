(set-logic QF_NRA)

(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)

(assert (> (+ (* x1 x1) (* x2 x3)) 10))
(assert (< (+ (* x2 x2 x2 x2) (* x1 x3)) 12))
(assert (< (+ (* x3 x3 x3) (* x1 x2)) 12))

(check-sat)
(get-model)