(set-logic QF_NRA)

(declare-const a Bool)
(declare-const y Real)
(declare-const z Real)

(assert (or (>= (* y z) 32) a))
(assert (<= (+ y z) 35))

(check-sat)
(get-model)
