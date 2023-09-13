(set-logic QF_NRA)

(declare-const skoc Real)
(declare-const skox Real)

(assert (>= (+ (* 235 skoc) (* 42 skox)) 0))
(assert (<= (+ (* 235 skoc) (* 42 skox)) 0))
(assert (= (+ (* skoc skoc) (* skox skox)) 1))

(check-sat)
(get-model)