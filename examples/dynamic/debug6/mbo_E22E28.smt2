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
(set-info :instance |E22E28|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= (+ (* 16 
(* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2
)) (* 16 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) h6
 (* j2 j2)) (* 4 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2)) (* 8 (* h1 h1 h1) h3 
(* h5 h5) (* j2 j2)) (* 4 (* h1 h1 h1) h3 (* h5 h5) j2) (* 8 (* h1 h1 h1) h3 h5 
h6 (* j2 j2 j2)) (* 16 (* h1 h1 h1) h3 h5 h6 (* j2 j2)) (* 8 (* h1 h1 h1) h3 h5 
h6 j2) (* 4 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2)) (* 8 (* h1 h1 h1) h3 (* h6 
h6) (* j2 j2)) (* 4 (* h1 h1 h1) h3 (* h6 h6) j2) (* (* h1 h1 h1) (* h5 h5) h6 
(* j2 j2 j2)) (* 3 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* 3 (* h1 h1 h1) (* h5 
h5) h6 j2) (* (* h1 h1 h1) (* h5 h5) h6) (* (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 
j2)) (* 3 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2)) (* 3 (* h1 h1 h1) h5 (* h6 h6) j2
) (* (* h1 h1 h1) h5 (* h6 h6)) (* 64 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2 j2))
 (* 80 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3) h5 
(* j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 80 (* h1 h1) (* 
h3 h3 h3) h6 (* j2 j2 j2)) (* 16 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2)) (* 48 (* 
h1 h1) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 56 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2)) 
(* 8 (* h1 h1) (* h3 h3) h4 h5 j2) (* 48 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2 j2))
 (* 44 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2)) (* 4 (* h1 h1) (* h3 h3) h4 h6 j2) 
(* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 72 (* h1 h1) (* h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 48 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2)) (* 8 (* 
h1 h1) (* h3 h3) (* h5 h5) j2) (* 64 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 144 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 96 (* h1 h1) (* h3 h3) h5 h6 
(* j2 j2)) (* 16 (* h1 h1) (* h3 h3) h5 h6 j2) (* 32 (* h1 h1) (* h3 h3) (* h6 
h6) (* j2 j2 j2 j2)) (* 72 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 48 (* 
h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) (* 8 (* h1 h1) (* h3 h3) (* h6 h6) j2) (* 
12 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2 j2)) (* 25 (* h1 h1) h3 h4 (* h5 h5) (* j2
 j2)) (* 14 (* h1 h1) h3 h4 (* h5 h5) j2) (* (* h1 h1) h3 h4 (* h5 h5)) (* 24 
(* h1 h1) h3 h4 h5 h6 (* j2 j2 j2)) (* 42 (* h1 h1) h3 h4 h5 h6 (* j2 j2)) (* 20
 (* h1 h1) h3 h4 h5 h6 j2) (* 2 (* h1 h1) h3 h4 h5 h6) (* 12 (* h1 h1) h3 h4 (* 
h6 h6) (* j2 j2 j2)) (* 18 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2)) (* 6 (* h1 h1) 
h3 h4 (* h6 h6) j2) (* 4 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 12 (* h1 
h1) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 12 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2)) (* 
4 (* h1 h1) h3 (* h5 h5 h5) j2) (* 16 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 51 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 57 (* h1 h1) h3 (* h5 h5) h6 
(* j2 j2)) (* 25 (* h1 h1) h3 (* h5 h5) h6 j2) (* 3 (* h1 h1) h3 (* h5 h5) h6) 
(* 16 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 51 (* h1 h1) h3 h5 (* h6 h6)
 (* j2 j2 j2)) (* 57 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2)) (* 25 (* h1 h1) h3 h5 
(* h6 h6) j2) (* 3 (* h1 h1) h3 h5 (* h6 h6)) (* 4 (* h1 h1) h3 (* h6 h6 h6) (* 
j2 j2 j2 j2)) (* 12 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) h3 
(* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1) h3 (* h6 h6 h6) j2) (* 3 (* h1 h1) h4 (* 
h5 h5) h6 (* j2 j2 j2)) (* 8 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2)) (* 7 (* h1 h1)
 h4 (* h5 h5) h6 j2) (* 2 (* h1 h1) h4 (* h5 h5) h6) (* 3 (* h1 h1) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 7 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2)) (* 5 (* h1 h1) h4 h5
 (* h6 h6) j2) (* (* h1 h1) h4 h5 (* h6 h6)) (* (* h1 h1) (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 4 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6 (* h1 h1) (* h5 h5 
h5) h6 (* j2 j2)) (* 4 (* h1 h1) (* h5 h5 h5) h6 j2) (* (* h1 h1) (* h5 h5 h5) 
h6) (* 2 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h1 h1) (* h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 (* 
h1 h1) (* h5 h5) (* h6 h6) j2) (* 2 (* h1 h1) (* h5 h5) (* h6 h6)) (* (* h1 h1) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 6 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2)) (* 4 (* h1 h1) h5 (* h6 h6 h6) j2) (* 
(* h1 h1) h5 (* h6 h6 h6)) (* 128 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 192 
h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 72 h1 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 8 
h1 (* h3 h3 h3) h4 h5 j2) (* 128 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 144 
h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 44 h1 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 4 
h1 (* h3 h3 h3) h4 h6 j2) (* 64 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 160 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 132 h1 (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2)) (* 40 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 4 h1 (* h3 h3 h3
) (* h5 h5) j2) (* 128 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 320 h1 (* h3
 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 264 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 80 
h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 8 h1 (* h3 h3 h3) h5 h6 j2) (* 64 h1 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 160 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2)) (* 132 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 40 h1 (* h3 h3 h3) (* 
h6 h6) (* j2 j2)) (* 4 h1 (* h3 h3 h3) (* h6 h6) j2) (* 48 h1 (* h3 h3) (* h4 h4
) h5 (* j2 j2 j2)) (* 64 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2)) (* 17 h1 (* h3 h3)
 (* h4 h4) h5 j2) (* h1 (* h3 h3) (* h4 h4) h5) (* 48 h1 (* h3 h3) (* h4 h4) h6 
(* j2 j2 j2)) (* 40 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2)) (* 6 h1 (* h3 h3) (* h4
 h4) h6 j2) (* 64 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 152 h1 (* h3 h3)
 h4 (* h5 h5) (* j2 j2 j2)) (* 114 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 28 h1
 (* h3 h3) h4 (* h5 h5) j2) (* 2 h1 (* h3 h3) h4 (* h5 h5)) (* 128 h1 (* h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2)) (* 284 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 204 h1 
(* h3 h3) h4 h5 h6 (* j2 j2)) (* 52 h1 (* h3 h3) h4 h5 h6 j2) (* 4 h1 (* h3 h3) 
h4 h5 h6) (* 64 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 124 h1 (* h3 h3) 
h4 (* h6 h6) (* j2 j2 j2)) (* 72 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 12 h1 
(* h3 h3) h4 (* h6 h6) j2) (* 16 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 52 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 60 h1 (* h3 h3) (* h5 h5 h5)
 (* j2 j2 j2)) (* 28 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 4 h1 (* h3 h3) (* 
h5 h5 h5) j2) (* 64 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 220 h1 (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 279 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2)) (* 157 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 37 h1 (* h3 h3) (* h5 h5) h6
 j2) (* 3 h1 (* h3 h3) (* h5 h5) h6) (* 64 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 220 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 279 h1 (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 157 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 37 h1 
(* h3 h3) h5 (* h6 h6) j2) (* 3 h1 (* h3 h3) h5 (* h6 h6)) (* 16 h1 (* h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 52 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 60 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 28 h1 (* h3 h3) (* h6 h6 h6) 
(* j2 j2)) (* 4 h1 (* h3 h3) (* h6 h6 h6) j2) (* 12 h1 h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2)) (* 26 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 16 h1 h3 (* h4 h4) 
(* h5 h5) j2) (* 2 h1 h3 (* h4 h4) (* h5 h5)) (* 24 h1 h3 (* h4 h4) h5 h6 (* j2 
j2 j2)) (* 36 h1 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 14 h1 h3 (* h4 h4) h5 h6 j2) 
(* 2 h1 h3 (* h4 h4) h5 h6) (* 12 h1 h3 (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 12 
h1 h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 2 h1 h3 (* h4 h4) (* h6 h6) j2) (* 8 h1 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 25 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2)) 
(* 27 h1 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 11 h1 h3 h4 (* h5 h5 h5) j2) (* h1 h3 
h4 (* h5 h5 h5)) (* 32 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 98 h1 h3 h4 (* 
h5 h5) h6 (* j2 j2 j2)) (* 106 h1 h3 h4 (* h5 h5) h6 (* j2 j2)) (* 46 h1 h3 h4 
(* h5 h5) h6 j2) (* 6 h1 h3 h4 (* h5 h5) h6) (* 32 h1 h3 h4 h5 (* h6 h6) (* j2 
j2 j2 j2)) (* 86 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 80 h1 h3 h4 h5 (* h6 h6)
 (* j2 j2)) (* 30 h1 h3 h4 h5 (* h6 h6) j2) (* 4 h1 h3 h4 h5 (* h6 h6)) (* 8 h1 
h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18 h1 h3 h4 (* h6 h6 h6) (* j2 j2 j2)) 
(* 12 h1 h3 h4 (* h6 h6 h6) (* j2 j2)) (* 2 h1 h3 h4 (* h6 h6 h6) j2) (* 8 h1 h3
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 34 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)
) (* 56 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 44 h1 h3 (* h5 h5 h5) h6 (* j2 j2
)) (* 16 h1 h3 (* h5 h5 h5) h6 j2) (* 2 h1 h3 (* h5 h5 h5) h6) (* 16 h1 h3 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 68 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2)) (* 112 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 88 h1 h3 (* h5 h5) (* h6 
h6) (* j2 j2)) (* 32 h1 h3 (* h5 h5) (* h6 h6) j2) (* 4 h1 h3 (* h5 h5) (* h6 h6
)) (* 8 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 34 h1 h3 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 56 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 44 h1 h3 h5 (* h6 
h6 h6) (* j2 j2)) (* 16 h1 h3 h5 (* h6 h6 h6) j2) (* 2 h1 h3 h5 (* h6 h6 h6)) 
(* 3 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 7 h1 (* h4 h4) (* h5 h5) h6 (* 
j2 j2)) (* 5 h1 (* h4 h4) (* h5 h5) h6 j2) (* h1 (* h4 h4) (* h5 h5) h6) (* 3 h1
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 5 h1 (* h4 h4) h5 (* h6 h6) (* j2 j2)) 
(* 2 h1 (* h4 h4) h5 (* h6 h6) j2) (* 2 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) 
(* 7 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 9 h1 h4 (* h5 h5 h5) h6 (* j2 j2)) 
(* 5 h1 h4 (* h5 h5 h5) h6 j2) (* h1 h4 (* h5 h5 h5) h6) (* 4 h1 h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2)) (* 14 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 18 
h1 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 10 h1 h4 (* h5 h5) (* h6 h6) j2) (* 2 h1
 h4 (* h5 h5) (* h6 h6)) (* 2 h1 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 h1 h4 
h5 (* h6 h6 h6) (* j2 j2 j2)) (* 6 h1 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 2 h1 h4 
h5 (* h6 h6 h6) j2) (* h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5 h1 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 10 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 5 h1 (* h5 h5 h5) (* h6 h6) j2)
 (* h1 (* h5 h5 h5) (* h6 h6)) (* h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 5 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10 h1 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2)) (* 10 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 5 h1 (* h5 h5) (* h6
 h6 h6) j2) (* h1 (* h5 h5) (* h6 h6 h6)) (* 64 (* h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2 j2)) (* 112 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 60 (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2)) (* 13 (* h3 h3 h3) (* h4 h4) h5 j2) (* (* h3 h3 h3) (* h4 
h4) h5) (* 64 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 64 (* h3 h3 h3) (* 
h4 h4) h6 (* j2 j2 j2)) (* 20 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 2 (* h3 h3
 h3) (* h4 h4) h6 j2) (* 64 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 176
 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 172 (* h3 h3 h3) h4 (* h5 h5) (* 
j2 j2 j2)) (* 73 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 14 (* h3 h3 h3) h4 (* 
h5 h5) j2) (* (* h3 h3 h3) h4 (* h5 h5)) (* 128 (* h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 352 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 344 (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2)) (* 146 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 28 (* h3 h3 h3) 
h4 h5 h6 j2) (* 2 (* h3 h3 h3) h4 h5 h6) (* 64 (* h3 h3 h3) h4 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 128 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 84 (* h3 h3 
h3) h4 (* h6 h6) (* j2 j2 j2)) (* 22 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 2 
(* h3 h3 h3) h4 (* h6 h6) j2) (* 64 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 240 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 348 (* h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 245 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 
87 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 15 (* h3 h3 h3) (* h5 h5) h6 j2) (* 
(* h3 h3 h3) (* h5 h5) h6) (* 64 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 240 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 348 (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 245 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 87 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 15 (* h3 h3 h3) h5 (* h6 h6) j2) (* (* 
h3 h3 h3) h5 (* h6 h6)) (* 16 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2)) (* 24 (* 
h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 9 (* h3 h3) (* h4 h4 h4) h5 j2) (* (* h3 h3
) (* h4 h4 h4) h5) (* 16 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2)) (* 12 (* h3 h3)
 (* h4 h4 h4) h6 (* j2 j2)) (* 2 (* h3 h3) (* h4 h4 h4) h6 j2) (* 32 (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 80 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2)) (* 66 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2)) (* 20 (* h3 h3) (* h4 h4)
 (* h5 h5) j2) (* 2 (* h3 h3) (* h4 h4) (* h5 h5)) (* 64 (* h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2)) (* 140 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2)) (* 103 (* h3 
h3) (* h4 h4) h5 h6 (* j2 j2)) (* 30 (* h3 h3) (* h4 h4) h5 h6 j2) (* 3 (* h3 h3
) (* h4 h4) h5 h6) (* 32 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2)) (* 52 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 26 (* h3 h3) (* h4 h4) (* h6 h6) 
(* j2 j2)) (* 4 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 16 (* h3 h3) h4 (* h5 h5 h5
) (* j2 j2 j2 j2 j2)) (* 56 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 73 (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 43 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2)) 
(* 11 (* h3 h3) h4 (* h5 h5 h5) j2) (* (* h3 h3) h4 (* h5 h5 h5)) (* 64 (* h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 220 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2)) (* 283 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2)) (* 166 (* h3 h3) h4 (* h5
 h5) h6 (* j2 j2)) (* 43 (* h3 h3) h4 (* h5 h5) h6 j2) (* 4 (* h3 h3) h4 (* h5 
h5) h6) (* 64 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 204 (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 243 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
133 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 33 (* h3 h3) h4 h5 (* h6 h6) j2) (* 
3 (* h3 h3) h4 h5 (* h6 h6)) (* 16 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2))
 (* 44 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 42 (* h3 h3) h4 (* h6 h6 h6
) (* j2 j2 j2)) (* 16 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2)) (* 2 (* h3 h3) h4 (* 
h6 h6 h6) j2) (* 16 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 129 (* h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 116 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 54 (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2)) (* 12 (* h3 h3) (* h5 h5 h5) h6 j2) (* (* h3 h3) (* h5 h5 
h5) h6) (* 32 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 144 (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 258 (* h3 h3) (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2)) (* 232 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 108 (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 24 (* h3 h3) (* h5 h5) (* h6 h6) j2) 
(* 2 (* h3 h3) (* h5 h5) (* h6 h6)) (* 16 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 72 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 129 (* h3 h3) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 116 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 54 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 12 (* h3 h3) h5 (* h6 h6 h6) j2) 
(* (* h3 h3) h5 (* h6 h6 h6)) (* 4 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2)) (* 9 
h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 6 h3 (* h4 h4 h4) (* h5 h5) j2) (* h3 
(* h4 h4 h4) (* h5 h5)) (* 8 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) (* 10 h3 (* h4 
h4 h4) h5 h6 (* j2 j2)) (* 2 h3 (* h4 h4 h4) h5 h6 j2) (* 4 h3 (* h4 h4 h4) (* 
h6 h6) (* j2 j2 j2)) (* 2 h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* 4 h3 (* h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 13 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 
15 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 7 h3 (* h4 h4) (* h5 h5 h5) j2) (* h3
 (* h4 h4) (* h5 h5 h5)) (* 16 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 47 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 49 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2
)) (* 21 h3 (* h4 h4) (* h5 h5) h6 j2) (* 3 h3 (* h4 h4) (* h5 h5) h6) (* 16 h3 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 35 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2
 j2)) (* 23 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 4 h3 (* h4 h4) h5 (* h6 h6) 
j2) (* 4 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 h3 (* h4 h4) (* h6 h6 
h6) (* j2 j2 j2)) (* 2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 8 h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 33 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 53 h3
 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 41 h3 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 15 
h3 h4 (* h5 h5 h5) h6 j2) (* 2 h3 h4 (* h5 h5 h5) h6) (* 16 h3 h4 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 63 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 
96 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 70 h3 h4 (* h5 h5) (* h6 h6) (* j2
 j2)) (* 24 h3 h4 (* h5 h5) (* h6 h6) j2) (* 3 h3 h4 (* h5 h5) (* h6 h6)) (* 8 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 26 h3 h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 30 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 14 h3 h4 h5 (* h6 h6 h6) 
(* j2 j2)) (* 2 h3 h4 h5 (* h6 h6 h6) j2) (* 4 h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 21 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 45 h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 50 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2)) (* 30 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 9 h3 (* h5 h5 h5) (* h6 h6) 
j2) (* h3 (* h5 h5 h5) (* h6 h6)) (* 4 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 21 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 45 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 50 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 
30 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 9 h3 (* h5 h5) (* h6 h6 h6) j2) (* h3
 (* h5 h5) (* h6 h6 h6)) (* (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2 (* h4 
h4 h4) (* h5 h5) h6 (* j2 j2)) (* (* h4 h4 h4) (* h5 h5) h6 j2) (* (* h4 h4 h4) 
h5 (* h6 h6) (* j2 j2 j2)) (* (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2)) (* (* h4 h4) (* h5 h5 h5) h6 j2) (* 2 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 (* h4 h4) (* h5 h5) (* h6 h6
) (* j2 j2 j2)) (* 6 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h4 h4) (* 
h5 h5) (* h6 h6) j2) (* (* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h4 h4
) h5 (* h6 h6 h6) (* j2 j2 j2)) (* (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h4 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 6 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* h4 (* h5 h5 h5) (* h6 h6) j2) (* h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 4 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 h4 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
h4 (* h5 h5) (* h6 h6 h6) j2)) 0)))
(check-sat)
(exit)
