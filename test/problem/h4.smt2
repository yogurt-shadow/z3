(set-logic QF_NRA)

(declare-const a Bool)
(declare-const b Bool)
(declare-const x Real)

(assert (or a (> x 12)))
(assert (or (< x 11) b))

(check-sat)
(get-model)
