(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)

; [0, 3]  [5, 9]

(assert (or (<= (+ (* x x) (* (- 3) x)) 0) (<= (+ (* x x) (* (- 14) x) 45) 0)))
(assert (< (* y y) (- (* (- 1) x) 1)))


(check-sat)
