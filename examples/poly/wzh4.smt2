(set-logic QF_NRA)

(declare-const v1 Real)
(declare-const v2 Real)
(declare-const v3 Real)
(declare-const v4 Real)

(assert (>= (+ (* v1 v1) (* v1 v3)) 10))
(assert (<= (+ (* v2 v2) (* v2 v3)) 12))
(assert (<= (+ (* v4 v4) (* v4 v3)) 8))

(check-sat)
(get-model)