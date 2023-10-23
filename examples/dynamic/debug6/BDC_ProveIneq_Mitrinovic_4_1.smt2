(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Ali K. Uncu, Matthew England, and James H. Davenport
Generated on: 2022-02-01

Generator: SUMCracker-ProveInequality function by Manuel Kauers ("https://www3.risc.jku.at/research/combinat/software/ergosum/RISC/SumCracker.html")
Translated to SMT-Lib by Maple SMTLIB package.

Application: Automated proof of (4.1) in 
D.S. Mitrinovic, Elementary Inequalities, P. Noordhoff ltd - Groningen, (1964)
("https://www.isinj.com/mt-usamo/Elementary%20Inequalities%20-%20Mitrinovic,%20et.%20al.%20(1964,%20Noordhoff).pdf")

All denominators in the original CAD call got cleared in a simple way:
a/b == c/d --> a d==b c && b<>0 && d<>0
a/b > c/d --> a d^2 >=b^2 c && b<>0 && d<>0
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status unsat)
(set-info :category "industrial")

(declare-fun V1 () Real)
(declare-fun V2 () Real)
(declare-fun V3 () Real)
(declare-fun V4 () Real)
(declare-fun V5 () Real)
(declare-fun V6 () Real)
(assert (and (= (* V1 V1) V5) (= (* V2 V2) (+ 1 V5)) (= (* V3 V3) (+ 1 V5)) (= (* V4 V4) (+ 2 V5)) (< 0 V1) (< 0 V2) (< 0 V3) (< 0 V4) (<= 1 V5) (<= 0 V5) (<= (+ (- 2) (* V3 2)) V6) (< (* V2 (+ (* V2 V6) 1)) (* (* (* V2 V2) (+ (- 1) V4)) 2)) (not (= V2 0))))
(check-sat)
(exit)







