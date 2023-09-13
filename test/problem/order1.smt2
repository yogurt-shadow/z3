(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-fun a () Bool)
(declare-fun b () Bool)

(assert (or (> (+ x (* x y)) 12) (< (+ y (* x x)) 9)))
(assert (and a (not b) (> (* x y y) 1)))

(check-sat)
(get-model)
