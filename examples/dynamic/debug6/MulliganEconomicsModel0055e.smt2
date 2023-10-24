(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Casey Mulligan, Russell Bradford, James H. Davenport, Matthew England, and ZakTonks
Generated on: 2018-04-19
Generator: TheoryGuru
Application: NGM: Permanent government purchases, example set
Target solver: Z3
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)

; Code written by TheoryGuru
; Mulligan model #0055
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
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v20 () Real)
(declare-fun v21 () Real)
(declare-fun v22 () Real)
(declare-fun v23 () Real)
(declare-fun v24 () Real)
(declare-fun v25 () Real)
(declare-fun v26 () Real)
(declare-fun v27 () Real)
(declare-fun v28 () Real)
(declare-fun v29 () Real)
(declare-fun v30 () Real)
(declare-fun v31 () Real)
(declare-fun v32 () Real)
(declare-fun v33 () Real)

; input assumptions
(define-fun assumptions () Bool (and 
(= v3 1)
(= v4 1)
(= v5 0)
(= v9 0)
(= (+ v5 (* v14 v5) (* v12 v7)) (+ v1 v3 v6))
(= (+ v6 (* v15 v6) (* v13 v8)) (+ v2 v4))
(= (+ (* v10 v12 (* v23 v23)) (* v1 v19 v27) (* (- 1) v21 v23 v7) (* (- 1) v16 (* v23 v23) v7) (* v19 v25 v7) (* v16 (* v23 v23) v32 v7)) (* v1 v23 v25))
(= (+ (* v11 v13 (* v24 v24)) (* v2 v20 v28) (* (- 1) v22 v24 v8) (* (- 1) v17 (* v24 v24) v8) (* v20 v26 v8) (* v17 (* v24 v24) v33 v8)) (* v2 v24 v26))
(= (+ (* v1 v27) (* 2 v1 v27 v31) (* v1 v27 (* v31 v31)) (* v25 v7) (* 2 v25 v31 v7) (* v25 (* v31 v31) v7) (* v24 v9) (* v15 v24 v9)) (+ (* v2 v28) (* v15 v2 v28) (* v2 v28 v31) (* v15 v2 v28 v31) (* v18 v24 v6) (* v18 v24 v31 v6) (* v26 v8) (* v15 v26 v8) (* v26 v31 v8) (* v15 v26 v31 v8)))
(= (+ (* v10 v12 v29) (* v12 v32 v7) (* v16 v29 v32 v7)) v3)
(= (+ (* v11 v13 v30) (* v13 v33 v8) (* v17 v30 v33 v8)) v4)
(> v12 0)
(> v13 0)
(> v15 0)
(> v23 0)
(> v24 0)
(> (* v19 v25) (* v21 v23))
(> (* v20 v26) (* v22 v24))
(> (* v21 v27) (* v25 v25))
(> (* v19 v27) (* v23 v25))
(> (* v22 v28) (* v26 v26))
(> (* v20 v28) (* v24 v26))
(> v29 0)
(> (+ v12 (* v16 v29)) 0)
(> v30 0)
(> (+ v13 (* v17 v30)) 0)
(> v31 (- 1))
(< v18 0)
(< v19 0)
(< v20 0)
(< v21 0)
(< v22 0)
(< v27 0)
(< v28 0)
(< v32 1)
(< v33 1)
(>= v32 0)
(>= v33 0)
(<= v10 0)
(<= v11 0)
(<= v16 0)
(<= v17 0)
))

; input hypothesis
(define-fun hypothesis () Bool
(> v7 0)
)

(assert assumptions)
(assert hypothesis)
(check-sat) ; checking the existence of an example to assumptions => hypothesis


(exit)