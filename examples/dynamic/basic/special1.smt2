(set-logic QF_NRA)

(declare-const x Real)
(declare-const y Real)
(declare-const z Real)

(assert (> z 1))
(assert (< z 10))
(assert (or (< (- 20 (* x x)) z) (< z (- (* y y) 10))))

(check-sat)
(get-model)

; z > 1
; z < 10
; z > 20 - x^2 \/ z < y^2 - 10