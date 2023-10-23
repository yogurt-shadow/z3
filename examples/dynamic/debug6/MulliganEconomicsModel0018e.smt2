(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Casey Mulligan, Russell Bradford, James H. Davenport, Matthew England, and ZakTonks
Generated on: 2018-04-19
Generator: TheoryGuru
Application: Supply-Demand: Becker irrational demand, example set
Target solver: Z3
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)

; Code written by TheoryGuru
; Mulligan model #0018
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

; input assumptions
(define-fun assumptions () Bool (and 
(= (+ (* v3 v5) (* v4 v7)) v1)
(= (+ (* v3 v6) (* v4 v8)) v2)
(= v2 v1)
(> v5 v6)
(> v3 0)
(> v4 0)
))

; input hypothesis
(define-fun hypothesis () Bool (< v7 v8))

(assert assumptions)
(assert hypothesis)
(check-sat) ; checking the existence of an example to assumptions => hypothesis


(exit)