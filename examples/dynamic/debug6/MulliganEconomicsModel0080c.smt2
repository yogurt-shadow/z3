(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Casey Mulligan, Russell Bradford, James H. Davenport, Matthew England, and ZakTonks
Generated on: 2018-04-19
Generator: TheoryGuru
Application: Vector mode: Consumer Theory Adding Up, counterexample set
Target solver: Z3
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unsat)

; Code written by TheoryGuru
; Mulligan model #0080
;   is part of the example library included in "Quantifier Elimination for Reasoning in Economics" April 2018
;   by Mulligan, Bradford, Davenport, England, and Tonks
;   available at bathpaper.economicreasoning.com .
; Economics background for this and other examples is provided at examples.economicreasoning.com .

(declare-fun v1 () Real)
(declare-fun v2 () Real)
(declare-fun v3 () Real)
(declare-fun v4 () Real)
(declare-fun v5 () Real)
(declare-fun v6 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)

; input assumptions
(define-fun assumptions () Bool (and 
(= (* v2 v5) 0)
(= (* v1 v9) v5)
(> v2 0)
(> v1 0)
(>= v3 0)
(>= v7 0)
(>= v10 0)
(>= v12 0)
(>= (* v3 v7) (* v4 v4))
(>= (* v10 v3) (* v5 v5))
(>= (* v12 v3) (* v6 v6))
(>= (* v10 v7) (* v8 v8))
(>= (* v12 v7) (* v9 v9))
(>= (* v10 v12) (* v11 v11))
(>= (+ (* v10 v3 v7) (* 2 v4 v5 v8)) (+ (* v10 (* v4 v4)) (* (* v5 v5) v7) (* v3 (* v8 v8))))
(>= (+ (* v12 v3 v7) (* 2 v4 v6 v9)) (+ (* v12 (* v4 v4)) (* (* v6 v6) v7) (* v3 (* v9 v9))))
(>= (+ (* v10 v12 v3) (* 2 v11 v5 v6)) (+ (* (* v11 v11) v3) (* v12 (* v5 v5)) (* v10 (* v6 v6))))
(>= (+ (* v10 v12 v7) (* 2 v11 v8 v9)) (+ (* (* v11 v11) v7) (* v12 (* v8 v8)) (* v10 (* v9 v9))))
(>= (+ (* (* v11 v11) (* v4 v4)) (* v10 v12 v3 v7) (* 2 v11 v5 v6 v7) (* 2 v12 v4 v5 v8) (* (* v6 v6) (* v8 v8)) (* 2 v10 v4 v6 v9) (* 2 v11 v3 v8 v9) (* (* v5 v5) (* v9 v9))) (+ (* v10 v12 (* v4 v4)) (* (* v11 v11) v3 v7) (* v12 (* v5 v5) v7) (* v10 (* v6 v6) v7) (* 2 v11 v4 v6 v8) (* v12 v3 (* v8 v8)) (* 2 v11 v4 v5 v9) (* 2 v5 v6 v8 v9) (* v10 v3 (* v9 v9))))
))

; input hypothesis
(define-fun hypothesis () Bool
(= v9 0)
)

(assert assumptions)
(assert (not hypothesis))

(check-sat) ; checking the existence of a counterexample to assumptions => hypothesis

(exit)