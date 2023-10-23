(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :author |Thomas Sturm, CNRS France, http://science.thomas-sturm.de|)
(set-info :source |
Transmitted by: Thomas Sturm
Generated on: 20161105
Received on: 20161105
Generator: RedLog, http://www.redlog.eu/
Application: qualitative analysis of systems of ODE in physics, chemistry, and the life sciences
Publication: Algebraic Biology 2008, doi:10.1007/978-3-540-85101-1_15
Additional information:
All problems have the following form: a certain polynomial has a zero where all variables are positive.  Interval solutions for satisfiable problems is a valuable information.
|)
(set-info :series |MBO - Methylene Blue Oscillator System|)
(set-info :instance |E11E18|)
(set-info :category "industrial")
(set-info :status sat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= 
(+ (* 8 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 36 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 40 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 
h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) 
h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1 h1) (* h2 h2 h2) h3
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 3 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2))) (- (* (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 
j2 j2 j2 j2))) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5 (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* (* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 
h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h2 h2) (* h3
 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 53 (* h1 h1 h1 h1) (* h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5
 h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 6 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (- (* 2 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2))) 
(- (* 6 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (- (* 2
 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2))) (* 8 (* h1 h1 h1 
h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1 
h1) (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1)
 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 3 (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2))) (- (* (* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2))) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 9 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 7 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 9 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
5 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 
h1 h1 h1) (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 
h1) (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 (* h1 h1 h1 h1) h2 (* 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h1 h1 h1 h1) h2 (* h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 16 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 88 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* 
h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) h2 
(* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) h2 (* h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 125 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 137 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 41 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 32
 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 
(* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 
h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1 h1 h1) 
h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1 h1) h2 (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1 h1) h2 (* h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) h2 (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 2 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 3 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (- (* (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2))) (- 
(* 3 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (- (* (* 
h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))) (* 4 (* h1 h1 h1 h1) 
h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1) h2 h3 h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 65 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 20 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1
 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* (* h1 h1 
h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 3 (* h1 h1 h1 
h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (- (* (* h1 h1 h1 h1) h2 h3
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2))) (* 16 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 2 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 7 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 25 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 29 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 9 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1
 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h1 
h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 
h1 h1) h2 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 2 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 9 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 14 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 9 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2 (* h1 h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 
(* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 
(* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* 
h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 
h1) h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1 h1) h2 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1 h1) h2 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1 h1) h2 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 88 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 40 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 8 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84
 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1
 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1 h1 h1
) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1 h1) (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2)) (* 6 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 4 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 22 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 50 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 20 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 12 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 70 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
84 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 
h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1)
 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 70 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1 h1 h1) (* h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 48 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 16 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 52 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 96 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 36 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32
 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 
(* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) 
h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h3 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h3 (* h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 4 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
18 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* 
h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1
) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) h3 h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1 h1 h1) h3 h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) h3 h4 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 20 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 16 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 4 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1)
 (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2 h2 
h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (- (* 2 (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 
j2 j2 j2 j2 j2))) (- (* (* h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 
j2))) (* (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 6 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* 
h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 180 (* h1 h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 108 (* h1 h1 h1) (* h2
 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 175 (* h1 h1 h1) (* h2 h2
 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 195 (* h1 h1 h1) (* h2 h2 
h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 63 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 43 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 123 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 117 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 37 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 89 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (- (* 3 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2
 j2 j2))) (- (* 11 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2
))) (- (* 4 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2))) (* 12 
(* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 
(* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* 
h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 
h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) (* h2
 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 37 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 57 (* h1 h1 h1) 
(* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43 (* h1 h1 h1) (* 
h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1) (* h2 h2 
h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2 h2) h3 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2 h2) h3 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 3 (* h1 h1 h1) (* h2 h2 h2) 
h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 9 (* h1 h1 h1) (* h2 h2 h2) 
h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (- (* 3 (* h1 h1 h1) (* h2 h2 h2) h3 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2))) (* 6 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 3 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 11 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 15 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 92 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 60 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 61 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 347
 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 643 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 291 (* h1
 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1
 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 372 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 189 (* h1 h1
 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 299 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 262 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1 h1
) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 328 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 438 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 172 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 131 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 425
 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 429 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 121 (* h1
 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 
h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 79 (* h1 
h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 243 
(* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
301 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
118 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 
(* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 44 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 154 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 172 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 54 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 2 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 37 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 104 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 95 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2)) (* 26 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 7 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 10 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (- (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2))) (- (* 10 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2 j2))) (- (* 3 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2))) (* 2 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 41 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 91 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 71 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 19 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16 (* 
h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 185
 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 
(* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 59 (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) 
(* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 
h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 6 (* h1 
h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 14 (* h1
 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (- (* 4 (* h1 h1
 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2))) (* 4 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* 
h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 41 (* h1 h1 h1) (* h2 h2) 
h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 91 (* h1 h1 h1) (* h2 h2) 
h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 83 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 73 (* h1 h1 h1) (* h2 h2) h3 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h1 h1 h1) (* h2 h2) h3 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) h3 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 2 (* h1 h1 h1) (* h2 h2) h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 4 (* h1 h1 h1) (* h2 h2) h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (- (* (* h1 h1 h1) (* h2 h2) h3 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))) (* 3 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) (* h2 h2) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h1 h1 h1) (* h2 h2) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) (* h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 138 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 
j2 j2 j2 j2 j2)) (* 90 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 96 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
80 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 
h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) 
h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1) h2 (* h3 
h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 261 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 433 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 165 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4
 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 570 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 248 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 77 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 451 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 891 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 402 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 
h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) h2
 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 536 (* h1 h1 h1) h2 (* h3 h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h1 h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 260 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 33 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 115 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 111 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 27 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 2 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 69 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 303 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 102 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 89 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 357 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 375 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 100 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2)) (* 34 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 158 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 174 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 50 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10 
(* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
126 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 431 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 664 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
249 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 
h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 63 (* 
h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 365 
(* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 433 
(* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 125 (* h1
 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 (* h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h2 (* h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) h2 (* h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) h2 (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h1 h1 h1) h2 (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 210 (* h1 h1 h1) h2 (* h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 354 (* h1 h1 h1) h2 (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 137 (* h1 h1 h1) h2 (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1 h1) h2 (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1) h2 (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (- (* (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2))) 
(- (* (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (* 14 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 53 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 
h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) 
h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h1 h1 h1) h2 h3
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 (* h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) h2 h3 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 h3 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 2 (* h1 h1 h1) h2 h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 2 (* h1 h1 h1) h2 h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (* 2 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 57 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 138 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 109 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 27 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 14 (* h1 
h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 161 
(* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 165 
(* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 45 (* h1 
h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h3
 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h3 h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* (* h1 h1 h1) h2 h3 h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* (* h1 h1 h1) h2 h3 h4 h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (* 8 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 36 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 78 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 68 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 18 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8
 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 24 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 62 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
64 (* h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* 
h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h2 (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1) h2 (* h4 h4) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1) h2 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) h2 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 7 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 3 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
(* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 
h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* 
h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* 
h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 
h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) 
h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) 
h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) (* h3 h3 h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4
 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 44 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 140 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 100 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* 
h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1) (* h3 h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3 h3 h3) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h3 h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2)) (* 12 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 72 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 116 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 40 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 20 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 124 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 188 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 52 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 32 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* 
h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 
h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1) (* h3
 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1 h1) (* 
h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 334 (* h1 h1 h1) (* h3
 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1 h1) (* h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1 h1) (* h3 h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) (* h3 h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 12 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 144 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 204 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 96 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 32 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 
(* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* 
h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 
h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1
 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* 
h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 
h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1)
 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1)
 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) 
(* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 142 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 134 (* h1 h1 h1
) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) (* h3
 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* 
h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h3 h3)
 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 114 (* h1 h1 h1) (* h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1 h1) (* h3 h3) 
h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h3 h3) h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h1 h1 h1) (* h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1) (* h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1) (* h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 8 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 4 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 
(* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* 
h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 
h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h3 (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h3 (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h3 h4 (* h5 h5
 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h3 h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 14 (* h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 4 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 8 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 12 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 20 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1
 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 
h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 
h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2 
h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) (* h2 h2 
h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2 h2)
 (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) 
h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3)
 h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 33 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5
 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 18 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2)) (* (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 14 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 34 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 11 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1
 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 4 (* h1 
h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (- (* 2 (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2))) (* 4 (* h1 h1) (* h2 h2 h2 h2) 
h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2 h2) 
h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2 h2) h3 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (- (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2))) (- (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2))) (* 2 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 2 (* h1 h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* (* h1 
h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* 
h1 h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 
h1) (* h2 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2
 h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 
h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 
h2 h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2
 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2) (* 
h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 
h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 274 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 488 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 267 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2
 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 264 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 158 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 246 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 126 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2
 j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 81 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 261 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 271 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 316 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 376 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 19 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 154 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 422 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 125 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 248 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 69 (* h1 h1) (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 169 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 155 (* h1 h1) (* h2 h2 h2
) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1) (* h2 h2 h2)
 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 126 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 (* h1 h1) (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2
 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2
) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* h2 h2 
h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 3 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 9 (* h1 h1) (* h2 
h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (- (* 3 (* h1 h1) (* h2 h2 
h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))) (* 3 (* h1 h1) (* h2 h2 h2) h3 h4
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h1 h1) (* h2 h2 h2) h3
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 89 (* h1 h1) (* h2 h2 h2) h3
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 73 (* h1 h1) (* h2 h2 h2) h3 h4
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 205 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 173 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (- (* 6 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2))) (- (* 16 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2))) (- (* 5 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2
 j2 j2 j2 j2))) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 9 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 43 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 81 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 69 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 22 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13 (* 
h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 48 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 78 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 64 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 21 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 5 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 7 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (- (* 3 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)))
 (- (* 7 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) 
(- (* 2 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))) (* 5 
(* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 18 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 14 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 3 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 5 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 18 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 24 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 14 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) 
(* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 33 (* 
h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45
 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
27 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 
(* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1
) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 
h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1)
 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1
 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* 
h1 h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 
h1) (* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) 
(* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* 
h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21
 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
13 (* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 
(* h1 h1) (* h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1
) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* 
h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 294 (* h1
 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 171 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1) (* h2 
h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2
) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 81 (* h1 h1) (* h2 h2) (* 
h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 114 (* h1 h1) (* h2 h2) (* h3
 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 674 (* h1 h1) (* h2 h2
) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1) (* h2 h2)
 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2) (* h3
 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 119 (* h1 h1) (* h2 
h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 495 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 793 (* h1 h1
) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 378 (* h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 201 (* h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 803 (* h1 h1
) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1227 (* h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 568 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1) (* h2
 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) (* h2
 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 95 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 383 (* h1 h1
) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 649 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) 
(* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 77 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
323 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 571 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 301 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7
 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 72 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 212 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 192 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2)) (* 45 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2
)) (* 14 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 167 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 466 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 499 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 166 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 23 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 196 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 604 (* h1 h1) (* h2 h2) (* h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 580 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 149 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 254 (* h1 h1) (* h2
 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h1 h1) (* 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 87 (* h1 h1) (* h2
 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 291 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 818 (* h1
 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 935 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 352 (* 
h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1
) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 169 
(* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 569 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 591 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 167 (* h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
8 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 24 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 13 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 87 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 213 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 257 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 102 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 21 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 358 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 440 (* h1 h1) (* h2 h2) (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 177 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2) (* h3 h3) h5
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* h1 h1) (* h2 h2) (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 177 (* h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 203 (* h1 h1) (* h2 h2
) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63 (* h1 h1) (* h2 h2) 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2) h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1) (* h2 h2)
 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 82 (* h1 h1) (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1) (* 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) (* h2
 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2) 
h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2
) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 2 (* h1 h1) (* h2 
h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 2 (* h1 h1) (* h2 
h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (* 6 (* h1 h1) (* h2 h2) h3
 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1) (* h2
 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 115 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 74 (* h1 h1)
 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1) (* h2
 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 105 (* h1 
h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 250 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
223 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
57 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 5 (* 
h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (- (* 5 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2))) (- (* 5 (* h1 h1) (* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2))) (* (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 15 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 27 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 13 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 22 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 115 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 224 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 173 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 42 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 31 (* 
h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 109 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 252 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 243 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 69 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 4 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (- (* 4 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2))) (- (* 4 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
)) (* 3 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 17 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 29 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 15 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
14 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 54 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 107 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 94 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 27 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 13 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 38 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 86 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 27 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (- (* (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2))) (- (* (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
) (* (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 4 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 5 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 5 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 14 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 13 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h1 h1) (* h2 h2) h4 (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2) h4 (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2) h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) (* h2 h2) h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2) h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2) (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 
h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 
h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) 
(* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 
h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 
h1) (* h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) 
(* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* 
h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 
(* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1
 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112
 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 202 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 111 (* h1
 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1) h2
 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) h2 
(* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1) h2 (* h3
 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h3 h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) h2 (* h3 h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 186 (* h1 h1) h2 (* h3 h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 420 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 261 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 32 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8
 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80
 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 232 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1
 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h2 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) h2 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 220 (* h1 h1) h2 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1) h2 (* h3
 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 41 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 147 (* h1 h1) h2 (* h3 h3
 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 167 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 (* h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 354 (* h1 h1) h2 (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 426 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 107 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 433 (* h1 h1) h2 (* h3 h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 533 (* h1 h1) h2 (* h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 151 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 198 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 177 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 675 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 863 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 322 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 5 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 82 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 430 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 566 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 181 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 16 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 16 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
40 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
176 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
224 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 88 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) 
h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 69 (* 
h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
325 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 435 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 175 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
16 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
144 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
200 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 
(* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2
 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1)
 h2 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1) h2
 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) h2
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 157 (* h1 
h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 (* 
h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1
 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) 
h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 
h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h1
 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1
) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 74 (* h1 
h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 186 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
132 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
21 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 21 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 193 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 471 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 413 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 78 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 5 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 51 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 211 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 165 (* h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 14 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 143 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 345 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 305 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 57 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
26 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 180 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 471 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 446 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 93 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 2 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 26 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 150 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 126 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 48 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 48 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
11 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 67 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 161 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 165 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 11 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 55 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 157 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 157 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2)) (* 4 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 40 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 3 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 10 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 7 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 14
 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36
 (* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 
(* h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 47 (* 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) h2 h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 59 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 126 (* h1 h1) h2 h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) h2 h3 (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1) h2 h3 (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 81 (* h1 h1) h2 h3
 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) h2 
h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) h2 h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) h2 h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) h2 h3 h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) h2 h3 h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 73 (* h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1) h2 h3 h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h1 h1) h2 h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h2 h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* 
h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 4 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 3 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 3 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 2 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 5 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 3 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
(* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2 (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
(* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 
h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 
h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1) (* 
h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h3 h3 h3 h3)
 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1) (* h3 h3 h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 10 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 78 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 126 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
58 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 
h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 
h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1)
 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h3
 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3 h3
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2)) (* 10 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 38 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 34 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 6 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 8 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 40 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 32 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
10 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 38 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 34 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 40 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 148 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 132 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 24 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
10 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 72 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 62 (* h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 8 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8
 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1
 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 110 (* 
h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 (* h1 
h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) 
(* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1) (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 (* h1 h1) (* 
h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 158 (* h1 h1) 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1) 
(* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) (* h3 
h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h3 h3 
h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h3 h3 h3) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) (* h3 h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h3 h3) (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h3 h3) (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h3 h3
) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) 
(* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1) (* h3 h3)
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 (* h1 h1) (* h3
 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h3
 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1)
 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 
h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 
h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1
) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* 
h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 
(* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* 
h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16
 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8
 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 
h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 
h1) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) 
h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1)
 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1)
 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1)
 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h3
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1) h3
 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h3 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 114 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 63 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 
j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 60 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 36 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
10 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 
h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 h1 (* 
h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 76 h1 (* h2 h2 h2 h2) (* h3 h3)
 (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4
 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 86 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2 j2 j2 j2)) (* 39 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 5 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 110 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 120 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 45 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2
 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2 h2
) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2 h2) (* h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2 h2 h2) (* h3
 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 (* h2 h2 h2 h2) (* h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2 h2) (* h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 32 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 10 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- 
(* 2 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (- (* h1 
(* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))) (* h1 (* h2 h2 h2 h2)
 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2 h2) h3 
h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 h1 (* h2 h2 h2 h2) h3 h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 5 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 60 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 50 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 15 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* 
h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2
 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 4 h1 (* h2 
h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (- (* 2 h1 (* h2 h2 h2 
h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2))) (* 2 h1 (* h2 h2 h2 h2) h3 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2 h2) h3 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2 h2) h3 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 3 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 18 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 5 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h1
 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 
(* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 2 h1 
(* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) (- (* h1 (* h2 h2 
h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2))) (* h1 (* h2 h2 h2 h2) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2 h2) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2
 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 
h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 
h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2 h2) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2 h2) (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 14 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
64 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 114 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 63 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2) (* h3 h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 h1 (* h2 h2 h2) (* h3 h3 h3 
h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 27 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 6 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 66 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 242 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 350 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 
168 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 h1 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h1
 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 380 h1 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 186 h1 (* h2
 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 432 h1 (* h2 h2 h2) (* 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 648 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 324 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5
 h6 (* j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 7 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 62 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 212 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 322 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 165 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
6 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 54 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 190 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 298 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
156 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 137 h1
 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 125 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 33 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 h1 (* h2
 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 270 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 282 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 102 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 19 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 147
 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
391 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
365 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 102 
h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 26 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 193 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 499 h1 (* h2 h2
 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 527 h1 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 195 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2 h2) (* h3 h3)
 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 141 h1 (* h2 h2 h2) (* h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 371 h1 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 355 h1 (* h2 h2 h2) (* h3
 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 105 h1 (* h2 h2 h2) (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 130 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 138 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 91 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 229 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 245 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 93 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 117 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 115 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 5 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 34 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 46 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 11 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
h1 (* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 
(* h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* h1 (* 
h2 h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* h1 (* h2 h2 
h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2))) (* 5 h1 (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 50 h1 (* h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 11 h1 (* h2 h2 h2) h3 (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 184 h1 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 h1 (* h2 h2 h2) h3 (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 38 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 3 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 3 h1 (* h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2))) (* h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 15 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 13 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 74 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 136 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 102
 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 h1 (* h2 
h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 21 h1 (* h2 h2 h2) h3 h4 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 98 h1 (* h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 (* h2 h2 h2) h3
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 142 h1 (* h2 h2 h2) h3 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 43 h1 (* h2 h2 h2) h3 h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* 3 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* 3 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2))) (* 2 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 8 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 36 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 64 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 52 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
16 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 h1 (* 
h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 
(* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 
(* h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 (* 
h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 
h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) h3 h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) h3 h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (- (* h1 (* h2 h2 h2) h3 h5 (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) (- (* h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2))) (* h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* h1 (* h2 h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 
h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 
h1 (* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 
(* h2 h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 
h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 (* 
h2 h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 
h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) 
(* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2
) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 142 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 220 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 111 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2
 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 134 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 226 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 120 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 5 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 60 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 250 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
420 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 225 h1 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2) (* h3 
h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 h1 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 114 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 200 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 114 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 166 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 172 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 116 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 342 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 138 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 159 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 477 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 505 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 153 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 6 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 63 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 181 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 193 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 69 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 25 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 218 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 642 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 730 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 273 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 18 h1
 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
150 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 456 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 494 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
162 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2) (* 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 57 h1 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 161 h1 (* h2 h2)
 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 183 h1 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2) (* h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 13 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 h1 (* h2 h2) (* h3
 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 300 h1 (* h2 h2) 
(* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 346 h1 (* h2 h2
) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 135 h1 (* h2 h2)
 (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) (* h3
 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 47 h1 (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 145 h1 (* h2 h2)
 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 161 h1 (* h2 h2) 
(* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 57 h1 (* h2 h2) (* h3 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 87 h1 (* h2 h2) (* h3 h3) (* h4
 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 131 h1 (* h2 h2) (* h3 h3
) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3) (* h4 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 h1 (* h2 h2) (* h3 h3) (* 
h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2) (* h3 h3) 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3) (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 91 h1 (* h2 h2) (* h3 h3)
 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 182 h1 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 139 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 38 h1 (* h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 245 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 509 h1 
(* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 391 
h1 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 81 h1
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* 
h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84
 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 228 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 156 h1 (* h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 22 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 50 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 38 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 26 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
166 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 339 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 276 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 57
 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h2
 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 229 
h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 484 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 389 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 90 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8
 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 52 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 152 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 108 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 
h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
21 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
49 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 
h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 14 h1 (* 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 75
 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 157 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 137 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 33 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
14 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 71 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 153 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 129 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 33 h1 (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 2 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 12 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 38 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 28 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 8 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 15 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 43 
h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 (* 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 h1 (* 
h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 h1 (* h2 h2) 
h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 130 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) h3 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2)
 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 h1 (* h2 h2
) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 h1 (* h2 h2) h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h2 h2) h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 21 h1 (* h2 h2) h3 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h2 h2) h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 131 h1 (* h2 h2) h3 h4 (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2) h3 h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 h1 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 (* h2 h2) h3 h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 17 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2 h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* h1 (* h2 h2) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 2 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* h1 (* h2 h2) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 3 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 6 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3 h1 (* h2 h2) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 4 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2 h1 (* h2 h2) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 6 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 3 h1 (* h2 h2) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 2 h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2 h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
10 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 
h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 h1 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 (* h3 h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 (* h3 h3 h3 h3) (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 116 h1 h2 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 46 h1 h2 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 120 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 50 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 10 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
42 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 h1 
h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 22 h1 h2 (* h3 
h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 226 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 93 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 18 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 88 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 126 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
55 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 h1 h2 (* h3
 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 h2 (* h3 h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h1 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 h2 (* h3 h3 h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 110 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 47 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 4 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 28 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 44 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 20
 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h1 h2 (* h3 h3 
h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 h2 (* h3 h3 h3
) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 (* h3 h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 46 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 h1 h2 (* h3 h3 h3) (* h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 82 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 3 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 93 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 65 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 5 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 50 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 116 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 86 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 15 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16 
h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
132 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 316 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 252 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 52
 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 h1 h2 (* 
h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 h1 h2 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 141 h1 h2
 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 105 h1 h2 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 h2 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 h2 (* h3 h3 
h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 h1 h2 (* h3 h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 11 h1 h2 (* h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 94 h1 h2 (* h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 37 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 17 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 126 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 308 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 258 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 59 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 21 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
95 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 75 h1 
h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 h2 (* h3 h3
 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 h2 (* h3 h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 h2 (* h3 h3 h3) (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 h1 h2 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 h1 h2 (* h3 h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 h2 (* h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 22 h1 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 22 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 4 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 24 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 20 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 
h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 
h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 
h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 
h2 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 h1 h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 h1 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 57 h1 h2 
(* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 h2 (* 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55 h1 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 91 h1 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 h1 h2 (* h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* h1 h2 (* h3 h3) (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 h2 (* h3 h3) (* h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 h1 h2 (* h3 h3) (* h4
 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 h2 (* h3 h3) (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 17 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 110 h1 h2 (* h3 h3) (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 171 h1 h2 (* h3 h3) (* h4 h4
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 70 h1 h2 (* h3 h3) (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 (* h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 81 h1 h2 (* h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 141 h1 h2 (* h3 h3) (* 
h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 75 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 h2 (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 33 h1 h2 (* h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 h1 h2 (* h3 h3) h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 h1 h2 (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 19 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 106 h1 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 171 h1 h2 (* h3 h3) h4 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h1 h2 (* h3 h3) h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 11 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 53 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 97 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 55 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 17 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 7 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 57 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 30 h1 h2 (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 3 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 13 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 25 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 15 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 5 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 3 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 
h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3
 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 h3 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23 h1 h2 h3 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 h2 h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 h2 h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 h2 h3 (* h4 h4) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 27 h1 h2 h3 (* h4 h4) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 h1 h2 h3 (* h4 h4) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 h2 h3 h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 h3 h4 (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 h1 h2 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 6 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 8 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 2 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 6 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 8 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 
h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 
h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 6 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 18 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 18 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 
h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h3 h3 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h3 h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h3 h3 h3 h3) h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3 h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 2 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 4 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2 h1 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 8 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4
 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3 h3) (* h4 h4)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 14 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 14 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 4 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 8 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 4 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 8 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 16 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
8 h1 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 
(* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3) 
(* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3) (* 
h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h3 h3) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h3 h3) (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h3 h3) (* h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h3 h3) h4 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h3 h3) h4 (* h5
 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h3 h3) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h3 h3) h4 (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3) (* h5 h5 h5 h5)
 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3) (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3) (* h5 h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 27 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 2 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 20 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 72 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 
(* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 
h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2 h2 h2) (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 22 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2)) (* 9 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 2 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 44 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 18 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2)) (* 3 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 66 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 72 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 27 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* (* h2 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* 
h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 
h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2 h2 h2) (* 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2 h2 h2) (* h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 h3) h4
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 9 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 2 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 44 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 18 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 22 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 9 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2
 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* 
h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* 
h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 
h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 
h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) h3 (* h4
 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2 h2) h3 (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 12 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 24 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 20 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 
(* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 h2
) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2
 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2
 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h2 h2 h2 h2
) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 h2 h2) h3 h4
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2 h2) h3 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2 h2) h3 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 36 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 54 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 27 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* (* h2 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2 h2)
 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 108 (* h2 h2 h2) (* h3 h3 h3 h3) h4
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 27 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)
) (* (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 10 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 36 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 54 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2
 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h2 h2
 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2 h2) (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2) (* h3 h3 h3) h4
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 2 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 44 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 18 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4
 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 32 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 88 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 36 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 2 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 16 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 44 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 48 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2)
 (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 
h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h2 h2 h2)
 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h2 h2
 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2 
h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2)
 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h2 h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h2 h2
 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h2 
h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 153 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
117 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
27 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 42 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 90 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 54 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 7 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 15 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 9 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
50 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
102 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 78
 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2
 h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h2 
h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 153 
(* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
117 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
27 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 
(* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 
(* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* 
h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2)
 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 h2) 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h2 h2 h2)
 (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h2 h2
 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 
h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 (* h2 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 
(* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 39
 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 
(* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2
 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h2 
h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2 
h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2) h3 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) 
h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2) 
h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2) h3 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2 h2) h3 (* 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h3 (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h3 (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) h3 (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 6 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 30 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 42 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 18 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 4 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 20 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 28 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 12 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 7 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3
 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* 
h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* 
h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2) h3
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h2 h2 h2) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2) 
h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3 h3)
 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3 h3)
 (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2) (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4)
 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 4 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 88 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 96 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 36 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 (* 
h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 66 
(* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 (* 
h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2)
 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3 
h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2) (* h3 h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3 h3) h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h2 h2) (* h3 h3 h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 25 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 25 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 153 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 117 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 54 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 75 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 153 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 117 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 7 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 15 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 25 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 51 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 39 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 25 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 51 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 39 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 7 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 15 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 9 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 10 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 14 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2) (* h3 h3) (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3) (* h4 h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) (* h5
 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2) (* h3 h3) (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 60
 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 84 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 36 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 20 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 28 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 12 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 84 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2) (* h3 h3) (* h5 h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) (* h3 h3) (* h5 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3) (* h5
 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3) (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2) (* h3 h3) 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) (* h3 
h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 (* h4 h4
 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) h3 (* h4 
h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 (* h4 h4 h4)
 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) h3 (* h4 h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h2 h2) h3 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) h3 
h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) 
h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h2 h2) h3 (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h3 h3 h3 h3) (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3 h3 h3) (* h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 18 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 36 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 30 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 9 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 2 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 12 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
24 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h2 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3
 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 h2 (* h3 h3 h3 h3) h4 (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 9 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 6 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 12 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 3 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h2 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 
(* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h2 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h2 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 h2 (* 
h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h2 (* h3 h3 
h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3)
 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 h2 (* h3 h3 h3) (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 h2 (* h3 h3 h3) (* h4 h4) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h2 (* h3 h3 h3) (* h4 h4)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h3 h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 h2 (* h3 h3 h3) h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 20 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 28 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 5 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 7 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 3 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 2 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 10 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 14 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 6 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 5 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 7 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3
 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h2 (* h3
 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 (* 
h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3)
 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 
h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 
h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h2 (* h3 
h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h2 (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h2
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2
 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12
 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 
h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 
h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 
h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h2 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h2 (* h3 
h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h2 (* 
h3 h3) (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))) 0)))
(check-sat)
(exit)
