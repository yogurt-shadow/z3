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
(set-info :instance |E20E22|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= (+ (* 12 
(* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h3 h3) h5 (* j2
 j2 j2)) (* 20 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2)) (* 4 (* h1 h1 h1) (* h3 h3) 
h5 j2) (* 12 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h3
 h3) h6 (* j2 j2 j2)) (* 20 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2)) (* 4 (* h1 h1 
h1) (* h3 h3) h6 j2) (* 4 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 16 
(* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h3 (* h5 h5) (* j2
 j2 j2)) (* 16 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2)) (* 4 (* h1 h1 h1) h3 (* h5 
h5) j2) (* 7 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 29 (* h1 h1 h1) h3 h5 
h6 (* j2 j2 j2 j2)) (* 46 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2)) (* 34 (* h1 h1 h1)
 h3 h5 h6 (* j2 j2)) (* 11 (* h1 h1 h1) h3 h5 h6 j2) (* (* h1 h1 h1) h3 h5 h6) 
(* 4 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h3 (* h6 
h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2)) (* 16 (* h1 
h1 h1) h3 (* h6 h6) (* j2 j2)) (* 4 (* h1 h1 h1) h3 (* h6 h6) j2) (* (* h1 h1 h1
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 15 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 20 (* h1 h1 h1) (* 
h5 h5) h6 (* j2 j2 j2)) (* 15 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* 6 (* h1 h1
 h1) (* h5 h5) h6 j2) (* (* h1 h1 h1) (* h5 h5) h6) (* (* h1 h1 h1) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15
 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20 (* h1 h1 h1) h5 (* h6 h6) (* 
j2 j2 j2)) (* 15 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2)) (* 6 (* h1 h1 h1) h5 (* h6
 h6) j2) (* (* h1 h1 h1) h5 (* h6 h6)) (* 12 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 
j2 j2)) (* 28 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 20 (* h1 h1) (* h3 h3 
h3) h5 (* j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3) h5 j2) (* 12 (* h1 h1) (* h3 h3 h3
) h6 (* j2 j2 j2 j2)) (* 28 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 20 (* h1 
h1) (* h3 h3 h3) h6 (* j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3) h6 j2) (* 7 (* h1 h1)
 (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 44 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2
 j2)) (* 78 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 52 (* h1 h1) (* h3 h3) h4
 h5 (* j2 j2)) (* 11 (* h1 h1) (* h3 h3) h4 h5 j2) (* 4 (* h1 h1) (* h3 h3) h4 
h6 (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 52 
(* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 36 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2
)) (* 8 (* h1 h1) (* h3 h3) h4 h6 j2) (* 8 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 48 (* h1 
h1) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 
j2)) (* 8 (* h1 h1) (* h3 h3) (* h5 h5) j2) (* 14 (* h1 h1) (* h3 h3) h5 h6 (* 
j2 j2 j2 j2 j2)) (* 57 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 92 (* h1 h1
) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 70 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2)) (* 22
 (* h1 h1) (* h3 h3) h5 h6 j2) (* (* h1 h1) (* h3 h3) h5 h6) (* 8 (* h1 h1) (* 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 
j2 j2 j2)) (* 44 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 36 (* h1 h1) (* 
h3 h3) (* h6 h6) (* j2 j2)) (* 12 (* h1 h1) (* h3 h3) (* h6 h6) j2) (* (* h1 h1)
 h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2
 j2 j2 j2)) (* 50 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2 j2)) (* 70 (* h1 h1) h3 
h4 (* h5 h5) (* j2 j2 j2)) (* 45 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2)) (* 11 (* 
h1 h1) h3 h4 (* h5 h5) j2) (* 2 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
20 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 62 (* h1 h1) h3 h4 h5 h6 (* j2 
j2 j2 j2)) (* 88 (* h1 h1) h3 h4 h5 h6 (* j2 j2 j2)) (* 62 (* h1 h1) h3 h4 h5 h6
 (* j2 j2)) (* 20 (* h1 h1) h3 h4 h5 h6 j2) (* 2 (* h1 h1) h3 h4 h5 h6) (* 4 (* 
h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h3 h4 (* h6 h6) (* j2
 j2 j2 j2)) (* 24 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1) h3 h4 
(* h6 h6) (* j2 j2)) (* 4 (* h1 h1) h3 h4 (* h6 h6) j2) (* 4 (* h1 h1) h3 (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
24 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 16 (* h1 h1) h3 (* h5 h5 h5) (* j2
 j2)) (* 4 (* h1 h1) h3 (* h5 h5 h5) j2) (* 3 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 23 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 (* h1 
h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 86 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2
)) (* 59 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2)) (* 19 (* h1 h1) h3 (* h5 h5) h6 j2
) (* 2 (* h1 h1) h3 (* h5 h5) h6) (* 3 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 22 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 61 (* h1 h1) h3 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 84 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 
61 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2)) (* 22 (* h1 h1) h3 h5 (* h6 h6) j2) (* 3
 (* h1 h1) h3 h5 (* h6 h6)) (* 4 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 16 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1) h3 (* h6 h6 h6)
 (* j2 j2 j2)) (* 16 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1) h3 (* 
h6 h6 h6) j2) (* 2 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 
h1) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 30 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 40 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 30 (* h1 h1) h4 (* h5 
h5) h6 (* j2 j2)) (* 12 (* h1 h1) h4 (* h5 h5) h6 j2) (* 2 (* h1 h1) h4 (* h5 h5
) h6) (* (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 20 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 15 (* h1 h1) h4 h5 (* h6 h6) 
(* j2 j2)) (* 6 (* h1 h1) h4 h5 (* h6 h6) j2) (* (* h1 h1) h4 h5 (* h6 h6)) (* 
(* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 15 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 20 (* h1
 h1) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2)) 
(* 6 (* h1 h1) (* h5 h5 h5) h6 j2) (* (* h1 h1) (* h5 h5 h5) h6) (* 2 (* h1 h1) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 30 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40 
(* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30 (* h1 h1) (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 12 (* h1 h1) (* h5 h5) (* h6 h6) j2) (* 2 (* h1 h1) (* h5 h5) (* 
h6 h6)) (* (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 20 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 15 (* h1 h1) h5 (* h6 h6 h6) 
(* j2 j2)) (* 6 (* h1 h1) h5 (* h6 h6 h6) j2) (* (* h1 h1) h5 (* h6 h6 h6)) (* 7
 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 32 h1 (* h3 h3 h3) h4 h5 (* j2 j2 
j2 j2)) (* 50 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 32 h1 (* h3 h3 h3) h4 h5 
(* j2 j2)) (* 7 h1 (* h3 h3 h3) h4 h5 j2) (* 4 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2
 j2 j2)) (* 16 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 24 h1 (* h3 h3 h3) h4 
h6 (* j2 j2 j2)) (* 16 h1 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 4 h1 (* h3 h3 h3) h4 
h6 j2) (* 4 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2)) (* 28 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 12 
h1 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 7 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 
j2)) (* 36 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 54 h1 (* h3 h3 h3) h5 h6 
(* j2 j2 j2)) (* 28 h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 3 h1 (* h3 h3 h3) h5 h6 
j2) (* 4 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2)) (* 24 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 16 h1 
(* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 4 h1 (* h3 h3 h3) (* h6 h6) j2) (* h1 (* h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2 j2)) (* 50 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 72 h1 (* h3 h3
) (* h4 h4) h5 (* j2 j2 j2)) (* 45 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 10 h1
 (* h3 h3) (* h4 h4) h5 j2) (* 4 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) 
(* 16 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 24 h1 (* h3 h3) (* h4 h4) h6
 (* j2 j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 4 h1 (* h3 h3) (* 
h4 h4) h6 j2) (* 2 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 22 h1 (* 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 68 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2
 j2 j2)) (* 92 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 58 h1 (* h3 h3) h4 (* 
h5 h5) (* j2 j2)) (* 14 h1 (* h3 h3) h4 (* h5 h5) j2) (* 4 h1 (* h3 h3) h4 h5 h6
 (* j2 j2 j2 j2 j2 j2)) (* 37 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 113 
h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 158 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2)
) (* 106 h1 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 29 h1 (* h3 h3) h4 h5 h6 j2) (* h1 
(* h3 h3) h4 h5 h6) (* 8 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 h1 
(* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 48 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2
 j2)) (* 32 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 8 h1 (* h3 h3) h4 (* h6 h6) 
j2) (* 4 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2)) (* 28 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 12 h1 
(* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 3 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 25 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 74 h1 (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 94 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 
51 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 9 h1 (* h3 h3) (* h5 h5) h6 j2) (* 3 
h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23 h1 (* h3 h3) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2)) (* 63 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 86 h1 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 61 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) 
(* 19 h1 (* h3 h3) h5 (* h6 h6) j2) (* h1 (* h3 h3) h5 (* h6 h6)) (* 4 h1 (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2
 j2)) (* 24 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 16 h1 (* h3 h3) (* h6 h6 
h6) (* j2 j2)) (* 4 h1 (* h3 h3) (* h6 h6 h6) j2) (* 2 h1 h3 (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 18 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
52 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 68 h1 h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 42 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 10 h1 h3 (* h4 h4) 
(* h5 h5) j2) (* 2 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 13 h1 h3 (* 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 33 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 42 h1 h3 (* h4 h4) h5 h6 (* j2 j2 j2)) (* 28 h1 h3 (* h4 h4) h5 h6 (* j2 j2))
 (* 9 h1 h3 (* h4 h4) h5 h6 j2) (* h1 h3 (* h4 h4) h5 h6) (* h1 h3 h4 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 11 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 34
 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 46 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2)
) (* 29 h1 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 7 h1 h3 h4 (* h5 h5 h5) j2) (* 6 h1 
h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 44 h1 h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 118 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 152 h1 h3 h4 (* h5 
h5) h6 (* j2 j2 j2)) (* 98 h1 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 28 h1 h3 h4 (* h5
 h5) h6 j2) (* 2 h1 h3 h4 (* h5 h5) h6) (* 4 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 26 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 66 h1 h3 h4 h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 84 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 56 h1 h3 h4
 h5 (* h6 h6) (* j2 j2)) (* 18 h1 h3 h4 h5 (* h6 h6) j2) (* 2 h1 h3 h4 h5 (* h6 
h6)) (* 2 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 14 h1 h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 36 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 44 h1 h3 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 26 h1 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 6 h1 h3 
(* h5 h5 h5) h6 j2) (* 4 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 26 
h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 66 h1 h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 84 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 56 h1 h3 (* h5
 h5) (* h6 h6) (* j2 j2)) (* 18 h1 h3 (* h5 h5) (* h6 h6) j2) (* 2 h1 h3 (* h5 
h5) (* h6 h6)) (* 2 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 13 h1 h3 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 33 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 42 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 28 h1 h3 h5 (* h6 h6 h6) (* j2 j2))
 (* 9 h1 h3 h5 (* h6 h6 h6) j2) (* h1 h3 h5 (* h6 h6 h6)) (* h1 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2))
 (* 15 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 20 h1 (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2)) (* 15 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 6 h1 (* h4 h4) 
(* h5 h5) h6 j2) (* h1 (* h4 h4) (* h5 h5) h6) (* h1 h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 6 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 h1 h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 20 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15 h1 h4
 (* h5 h5 h5) h6 (* j2 j2)) (* 6 h1 h4 (* h5 h5 h5) h6 j2) (* h1 h4 (* h5 h5 h5)
 h6) (* 2 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 h4 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 40 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30 h1 h4 (* h5 h5) (* h6 h6) 
(* j2 j2)) (* 12 h1 h4 (* h5 h5) (* h6 h6) j2) (* 2 h1 h4 (* h5 h5) (* h6 h6)) 
(* h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 15 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 20 
h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 15 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2
)) (* 6 h1 (* h5 h5 h5) (* h6 h6) j2) (* h1 (* h5 h5 h5) (* h6 h6)) (* h1 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 15 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 h1 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 15 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6 h1 
(* h5 h5) (* h6 h6 h6) j2) (* h1 (* h5 h5) (* h6 h6 h6)) (* (* h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 7 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2))
 (* 18 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 22 (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2)) (* 13 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2)) (* 3 (* h3 h3 h3) 
(* h4 h4) h5 j2) (* (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 22 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2
 j2 j2)) (* 24 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 9 (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2)) (* 2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 14 (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 36 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2))
 (* 44 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 26 (* h3 h3 h3) h4 h5 h6 (* j2 j2)
) (* 6 (* h3 h3 h3) h4 h5 h6 j2) (* (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 8 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22 (* h3 h3 h3) (* h5
 h5) h6 (* j2 j2 j2 j2)) (* 24 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 9 (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2
 j2)) (* 7 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18 (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 22 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 13 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 3 (* h3 h3 h3) h5 (* h6 h6) j2) (* (* h3
 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 7 (* h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2)) (* 18 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 22 (* h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2)) (* 13 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 3 
(* h3 h3) (* h4 h4 h4) h5 j2) (* 2 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 14 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 36 (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 44 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 26 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 6 (* h3 h3) (* h4 h4) 
(* h5 h5) j2) (* 3 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 21 (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 54 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2
 j2 j2)) (* 66 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 39 (* h3 h3) (* h4 h4)
 h5 h6 (* j2 j2)) (* 9 (* h3 h3) (* h4 h4) h5 h6 j2) (* (* h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
22 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 24 (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2)) (* 9 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) (* 4 (* h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)
) (* 72 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 88 (* h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2)) (* 52 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 12 (* h3 h3) h4 
(* h5 h5) h6 j2) (* 3 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 21 (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 54 (* h3 h3) h4 h5 (* h6 h6) (* j2
 j2 j2 j2)) (* 66 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 39 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2)) (* 9 (* h3 h3) h4 h5 (* h6 h6) j2) (* (* h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 22 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 24 (* h3 h3) (* h5 h5 h5) h6
 (* j2 j2 j2)) (* 9 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 2 (* h3 h3) (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 36 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 44 (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 26 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2))
 (* 6 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 7 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18 (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 13 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 3 (* h3 h3) h5 (* h6 h6 h6) j2) 
(* h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 7 h3 (* h4 h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 18 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 22 
h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 13 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2
)) (* 3 h3 (* h4 h4 h4) (* h5 h5) j2) (* h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2)) (* 7 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 18 h3 (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 22 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 
13 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 3 h3 (* h4 h4) (* h5 h5 h5) j2) (* 3 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 21 h3 (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2)) (* 54 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 66 h3 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 39 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2)) 
(* 9 h3 (* h4 h4) (* h5 h5) h6 j2) (* 2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 14 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 36 h3 h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2)) (* 44 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 26 h3 h4 (* h5 h5
 h5) h6 (* j2 j2)) (* 6 h3 h4 (* h5 h5 h5) h6 j2) (* 3 h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 21 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
54 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 66 h3 h4 (* h5 h5) (* h6 h6) 
(* j2 j2 j2)) (* 39 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 9 h3 h4 (* h5 h5) 
(* h6 h6) j2) (* h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 22 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 13 h3 (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 3 h3 (* h5 h5 h5) (* h6 h6) j2) (* h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 7 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18 
h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 22 h3 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 13 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 3 h3 (* h5 h5) (* h6 h6 
h6) j2)) 0)))
(check-sat)
(exit)
