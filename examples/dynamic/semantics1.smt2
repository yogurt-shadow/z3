(set-logic QF_NRA)

(declare-const y Real)
(declare-const x Real)

; feasible set:
; [-2, -1] [-4, -3]
; [-8, -7] [-6, -5]

(assert (or (<= (+ (* y y) (* 3 y) 2) x) (<= (+ (* y y) (* 7 y) 12) 0)))
(assert (or (<= (+ (* y y) (* 15 y) 56) x) (<= (+ (* y y) (* 11 y) 30) 0)))

(check-sat)
