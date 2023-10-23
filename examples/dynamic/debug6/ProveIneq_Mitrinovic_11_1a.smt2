(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Ali K. Uncu, Matthew England, and James H. Davenport
Generated on: 2022-01-05

Generator: SUMCracker-ProveInequality function by Manuel Kauers ("https://www3.risc.jku.at/research/combinat/software/ergosum/RISC/SumCracker.html")
Translated to SMT-Lib by Maple SMTLIB package.

Application: Automated proof of (11.1) in 
D.S. Mitrinovic, Elementary Inequalities, P. Noordhoff ltd - Groningen, (1964)
("https://www.isinj.com/mt-usamo/Elementary%20Inequalities%20-%20Mitrinovic,%20et.%20al.%20(1964,%20Noordhoff).pdf")

|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-info :category "industrial")

(declare-fun V1 () Real)
(declare-fun V2 () Real)
(declare-fun V3 () Real)
(declare-fun V4 () Real)
(declare-fun V5 () Real)
(declare-fun V6 () Real)
(declare-fun V7 () Real)
(declare-fun V8 () Real)
(declare-fun V9 () Real)
(declare-fun V10 () Real)
(assert (and (= (* V2 V2) (+ 1 V1 V9)) (= (* V3 V3) (+ 2 V2 V9)) (= (* V5 V5) V9) (= (* V6 V6) (+ 1 V9)) (= (* V7 V7) (+ 1 V10)) (= (* V8 V8) (+ 2 V10)) (< 0 V1) (< 0 V2) (< 0 V3) (< 0 V4) (<= 1 V9) (<= 0 V9) (<= 0 V10) (<= 0 (+ 1 V10)) (< 0 V5) (< 0 V6) (< 0 V7) (< 0 V8) (< V1 (+ 1 V5)) (< V2 (+ 1 V6)) (<= (+ 1 V7) V3)))
(check-sat)
(exit)




























