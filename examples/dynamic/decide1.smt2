(set-logic QF_NRA)

(declare-const x Real)

; feasible set:
; [-8, -5] [-4, -1] [-10 -9] [-12 -11] [2, 10]
; [-8, -6] [4, 5]
; [3, 6]

(assert (or (<= (+ (* x x) (* 13 x) 40) 0) (<= (+ (* x x) (* 5 x) 4) 0) (<= (+ (* x x) (* 19 x) 90) 0) (<= (+ (* x x) (* 23 x) 132) 0) (<= (+ (* x x) (* (- 12) x) 20) 0)))
(assert (or (<= (+ (* x x) (* 14 x) 48) 0) (<= (+ (* x x) (* (- 9) x) 20) 0)))
(assert (<= (+ (* x x) (* (- 9) x) 18) 0))


(check-sat)
(get-model)
