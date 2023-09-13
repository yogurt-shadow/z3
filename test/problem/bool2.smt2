(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

(assert (or (not a) b))
(assert (or (not c) a))
(assert (or a (> (+ (* x y) y) 12)))
(assert (or b (<= (+ (* x y) y) 12)))
(assert (or c (> (+ x y) (- 3))))

(check-sat)
