(set-logic QF_NRA)

(declare-const x Real)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(assert (< (+ (* a x x) (* b x) c) 0))

(check-sat)
(get-model)
