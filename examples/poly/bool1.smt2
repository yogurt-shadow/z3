(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-fun a () Bool)
(declare-fun b () Bool)

(assert a)
(assert (or a b))
(assert (or a (> (+ (* x y) y) 12)))
(assert (or b (<= (+ (* x y) y) 12)))

(check-sat)
