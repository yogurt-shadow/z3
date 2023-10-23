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
(set-info :instance |E16E28|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h5 0) (> h6 0) (> j2 0) (= (+ (* 16 
(* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2)) (* 20 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2
)) (* 6 (* h1 h1 h1) (* h3 h3) h5 j2) (* 16 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 
j2)) (* 32 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2)) (* 20 (* h1 h1 h1) (* h3 h3) h6 
j2) (* 4 (* h1 h1 h1) (* h3 h3) h6) (* 4 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2))
 (* 3 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2)) (* 8 (* h1 h1 h1) h3 h5 h6 (* j2 j2 
j2)) (* 11 (* h1 h1 h1) h3 h5 h6 (* j2 j2)) (* 5 (* h1 h1 h1) h3 h5 h6 j2) (* 4 
(* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2)) (* 10 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2
)) (* 8 (* h1 h1 h1) h3 (* h6 h6) j2) (* 2 (* h1 h1 h1) h3 (* h6 h6)) (* (* h1 
h1 h1) (* h5 h5) h6 (* j2 j2 j2)) (* (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* (* 
h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2)) (* 2 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2)) 
(* (* h1 h1 h1) h5 (* h6 h6) j2) (* 48 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2)) 
(* 64 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2)) (* 23 (* h1 h1) h2 (* h3 h3) h5 j2) 
(* 2 (* h1 h1) h2 (* h3 h3) h5) (* 48 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2)) 
(* 92 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2)) (* 46 (* h1 h1) h2 (* h3 h3) h6 j2) 
(* 6 (* h1 h1) h2 (* h3 h3) h6) (* 12 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2)) 
(* 15 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2)) (* 4 (* h1 h1) h2 h3 (* h5 h5) j2) 
(* 24 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2)) (* 40 (* h1 h1) h2 h3 h5 h6 (* j2 j2))
 (* 23 (* h1 h1) h2 h3 h5 h6 j2) (* 5 (* h1 h1) h2 h3 h5 h6) (* 12 (* h1 h1) h2 
h3 (* h6 h6) (* j2 j2 j2)) (* 30 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2)) (* 22 (* 
h1 h1) h2 h3 (* h6 h6) j2) (* 4 (* h1 h1) h2 h3 (* h6 h6)) (* 3 (* h1 h1) h2 (* 
h5 h5) h6 (* j2 j2 j2)) (* 5 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1)
 h2 (* h5 h5) h6 j2) (* 3 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2)) (* 7 (* h1 h1)
 h2 h5 (* h6 h6) (* j2 j2)) (* 5 (* h1 h1) h2 h5 (* h6 h6) j2) (* (* h1 h1) h2 
h5 (* h6 h6)) (* 64 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 112 (* h1 h1) 
(* h3 h3 h3) h5 (* j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2)) (* 12 
(* h1 h1) (* h3 h3 h3) h5 j2) (* 64 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) 
(* 160 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 144 (* h1 h1) (* h3 h3 h3) h6 
(* j2 j2)) (* 56 (* h1 h1) (* h3 h3 h3) h6 j2) (* 8 (* h1 h1) (* h3 h3 h3) h6) 
(* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 68 (* h1 h1) (* h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 49 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2)) (* 12 (* 
h1 h1) (* h3 h3) (* h5 h5) j2) (* 64 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) 
(* 172 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 175 (* h1 h1) (* h3 h3) h5 h6 
(* j2 j2)) (* 71 (* h1 h1) (* h3 h3) h5 h6 j2) (* 10 (* h1 h1) (* h3 h3) h5 h6) 
(* 32 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 100 (* h1 h1) (* h3 h3) 
(* h6 h6) (* j2 j2 j2)) (* 106 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) (* 44 
(* h1 h1) (* h3 h3) (* h6 h6) j2) (* 6 (* h1 h1) (* h3 h3) (* h6 h6)) (* 4 (* h1
 h1) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 7 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2
)) (* 3 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2)) (* 16 (* h1 h1) h3 (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 38 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 31 (* h1 h1) h3 
(* h5 h5) h6 (* j2 j2)) (* 9 (* h1 h1) h3 (* h5 h5) h6 j2) (* 16 (* h1 h1) h3 h5
 (* h6 h6) (* j2 j2 j2 j2)) (* 51 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 61 
(* h1 h1) h3 h5 (* h6 h6) (* j2 j2)) (* 31 (* h1 h1) h3 h5 (* h6 h6) j2) (* 5 
(* h1 h1) h3 h5 (* h6 h6)) (* 4 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 14
 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 18 (* h1 h1) h3 (* h6 h6 h6) (* j2 
j2)) (* 10 (* h1 h1) h3 (* h6 h6 h6) j2) (* 2 (* h1 h1) h3 (* h6 h6 h6)) (* (* 
h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 2 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 
j2)) (* (* h1 h1) (* h5 h5 h5) h6 (* j2 j2)) (* 2 (* h1 h1) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 6 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6 (* h1 h1)
 (* h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h1 h1) (* h5 h5) (* h6 h6) j2) (* (* h1 
h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2)
) (* 3 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2)) (* (* h1 h1) h5 (* h6 h6 h6) j2) (* 
48 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 68 h1 (* h2 h2) (* h3 h3) h5 (* j2
 j2)) (* 26 h1 (* h2 h2) (* h3 h3) h5 j2) (* 3 h1 (* h2 h2) (* h3 h3) h5) (* 48 
h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 88 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2
)) (* 32 h1 (* h2 h2) (* h3 h3) h6 j2) (* 2 h1 (* h2 h2) (* h3 h3) h6) (* 12 h1 
(* h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 21 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2)) 
(* 10 h1 (* h2 h2) h3 (* h5 h5) j2) (* h1 (* h2 h2) h3 (* h5 h5)) (* 24 h1 (* h2
 h2) h3 h5 h6 (* j2 j2 j2)) (* 47 h1 (* h2 h2) h3 h5 h6 (* j2 j2)) (* 30 h1 (* 
h2 h2) h3 h5 h6 j2) (* 7 h1 (* h2 h2) h3 h5 h6) (* 12 h1 (* h2 h2) h3 (* h6 h6) 
(* j2 j2 j2)) (* 30 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2)) (* 20 h1 (* h2 h2) h3 
(* h6 h6) j2) (* 2 h1 (* h2 h2) h3 (* h6 h6)) (* 3 h1 (* h2 h2) (* h5 h5) h6 (* 
j2 j2 j2)) (* 7 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2)) (* 5 h1 (* h2 h2) (* h5 h5)
 h6 j2) (* h1 (* h2 h2) (* h5 h5) h6) (* 3 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2
)) (* 8 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2)) (* 7 h1 (* h2 h2) h5 (* h6 h6) j2) 
(* 2 h1 (* h2 h2) h5 (* h6 h6)) (* 128 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2)) 
(* 240 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2)) (* 156 h1 h2 (* h3 h3 h3) h5 (* j2 j2
)) (* 42 h1 h2 (* h3 h3 h3) h5 j2) (* 4 h1 h2 (* h3 h3 h3) h5) (* 128 h1 h2 (* 
h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 304 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2)) (* 224 
h1 h2 (* h3 h3 h3) h6 (* j2 j2)) (* 60 h1 h2 (* h3 h3 h3) h6 j2) (* 4 h1 h2 (* 
h3 h3 h3) h6) (* 64 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 156 h1 h2 (* 
h3 h3) (* h5 h5) (* j2 j2 j2)) (* 131 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2)) (* 43
 h1 h2 (* h3 h3) (* h5 h5) j2) (* 4 h1 h2 (* h3 h3) (* h5 h5)) (* 128 h1 h2 (* 
h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 352 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2)) (* 350 
h1 h2 (* h3 h3) h5 h6 (* j2 j2)) (* 138 h1 h2 (* h3 h3) h5 h6 j2) (* 18 h1 h2 
(* h3 h3) h5 h6) (* 64 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 196 h1 h2 
(* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 194 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2)) 
(* 66 h1 h2 (* h3 h3) (* h6 h6) j2) (* 8 h1 h2 (* h3 h3) (* h6 h6)) (* 8 h1 h2 
h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 20 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2)) (* 16
 h1 h2 h3 (* h5 h5 h5) (* j2 j2)) (* 4 h1 h2 h3 (* h5 h5 h5) j2) (* 32 h1 h2 h3 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 93 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2)) (* 99 h1
 h2 h3 (* h5 h5) h6 (* j2 j2)) (* 47 h1 h2 h3 (* h5 h5) h6 j2) (* 9 h1 h2 h3 (* 
h5 h5) h6) (* 32 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 107 h1 h2 h3 h5 (* h6
 h6) (* j2 j2 j2)) (* 132 h1 h2 h3 h5 (* h6 h6) (* j2 j2)) (* 67 h1 h2 h3 h5 (* 
h6 h6) j2) (* 10 h1 h2 h3 h5 (* h6 h6)) (* 8 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 28 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2)) (* 34 h1 h2 h3 (* h6 h6 h6) (* j2
 j2)) (* 16 h1 h2 h3 (* h6 h6 h6) j2) (* 2 h1 h2 h3 (* h6 h6 h6)) (* 2 h1 h2 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 6 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6 h1 
h2 (* h5 h5 h5) h6 (* j2 j2)) (* 2 h1 h2 (* h5 h5 h5) h6 j2) (* 4 h1 h2 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 14 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 18
 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2)) (* 10 h1 h2 (* h5 h5) (* h6 h6) j2) (* 2 
h1 h2 (* h5 h5) (* h6 h6)) (* 2 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7 h1 
h2 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 9 h1 h2 h5 (* h6 h6 h6) (* j2 j2)) (* 5 h1 
h2 h5 (* h6 h6 h6) j2) (* h1 h2 h5 (* h6 h6 h6)) (* 64 h1 (* h3 h3 h3) (* h5 h5)
 (* j2 j2 j2 j2 j2)) (* 176 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 176 h1
 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 76 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2))
 (* 12 h1 (* h3 h3 h3) (* h5 h5) j2) (* 128 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2
 j2)) (* 464 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 628 h1 (* h3 h3 h3) h5 h6
 (* j2 j2 j2)) (* 386 h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 110 h1 (* h3 h3 h3) h5
 h6 j2) (* 12 h1 (* h3 h3 h3) h5 h6) (* 64 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 240 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 320 h1 (* h3 h3 h3
) (* h6 h6) (* j2 j2 j2)) (* 188 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 48 h1 
(* h3 h3 h3) (* h6 h6) j2) (* 4 h1 (* h3 h3 h3) (* h6 h6)) (* 16 h1 (* h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 52 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)
) (* 62 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 32 h1 (* h3 h3) (* h5 h5 h5) 
(* j2 j2)) (* 6 h1 (* h3 h3) (* h5 h5 h5) j2) (* 64 h1 (* h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 236 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 349 h1 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 248 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2))
 (* 79 h1 (* h3 h3) (* h5 h5) h6 j2) (* 8 h1 (* h3 h3) (* h5 h5) h6) (* 64 h1 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 264 h1 (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 410 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 289 h1 (* h3 h3)
 h5 (* h6 h6) (* j2 j2)) (* 90 h1 (* h3 h3) h5 (* h6 h6) j2) (* 11 h1 (* h3 h3) 
h5 (* h6 h6)) (* 16 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 68 h1 (* h3
 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 106 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)
) (* 74 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 22 h1 (* h3 h3) (* h6 h6 h6) j2)
 (* 2 h1 (* h3 h3) (* h6 h6 h6)) (* 8 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 28 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 36 h1 h3 (* h5 h5 h5) h6 (* j2 
j2 j2)) (* 20 h1 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 4 h1 h3 (* h5 h5 h5) h6 j2) 
(* 16 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 67 h1 h3 (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 113 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 93 h1 h3 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 35 h1 h3 (* h5 h5) (* h6 h6) j2) (* 4 h1 h3 
(* h5 h5) (* h6 h6)) (* 8 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 h1 h3 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 63 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 53
 h1 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 21 h1 h3 h5 (* h6 h6 h6) j2) (* 3 h1 h3 h5 
(* h6 h6 h6)) (* h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h1 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4
 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* h1 (* h5 h5 h5) (* h6 h6) j2) (* h1 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 6 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 h1 (* h5 h5) (* h6 h6 
h6) (* j2 j2)) (* h1 (* h5 h5) (* h6 h6 h6) j2) (* 16 (* h2 h2 h2) (* h3 h3) h5 
(* j2 j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2)) (* 9 (* h2 h2 h2) (* h3
 h3) h5 j2) (* (* h2 h2 h2) (* h3 h3) h5) (* 16 (* h2 h2 h2) (* h3 h3) h6 (* j2 
j2 j2)) (* 28 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 6 (* h2 h2 h2) (* h3 h3) 
h6 j2) (* 4 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 9 (* h2 h2 h2) h3 (* h5 
h5) (* j2 j2)) (* 6 (* h2 h2 h2) h3 (* h5 h5) j2) (* (* h2 h2 h2) h3 (* h5 h5)) 
(* 8 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 18 (* h2 h2 h2) h3 h5 h6 (* j2 j2)) 
(* 12 (* h2 h2 h2) h3 h5 h6 j2) (* 2 (* h2 h2 h2) h3 h5 h6) (* 4 (* h2 h2 h2) h3
 (* h6 h6) (* j2 j2 j2)) (* 10 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 6 (* h2 
h2 h2) h3 (* h6 h6) j2) (* (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 3 (* h2 h2
 h2) (* h5 h5) h6 (* j2 j2)) (* 3 (* h2 h2 h2) (* h5 h5) h6 j2) (* (* h2 h2 h2) 
(* h5 h5) h6) (* (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 3 (* h2 h2 h2) h5 
(* h6 h6) (* j2 j2)) (* 3 (* h2 h2 h2) h5 (* h6 h6) j2) (* (* h2 h2 h2) h5 (* h6
 h6)) (* 64 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 128 (* h2 h2) (* h3 h3
 h3) h5 (* j2 j2 j2)) (* 84 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 22 (* h2 h2)
 (* h3 h3 h3) h5 j2) (* 2 (* h2 h2) (* h3 h3 h3) h5) (* 64 (* h2 h2) (* h3 h3 h3
) h6 (* j2 j2 j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 80 (* h2
 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) h6 j2) (* 32 (* h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 88 (* h2 h2) (* h3 h3) (* h5 h5) (* 
j2 j2 j2)) (* 84 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 32 (* h2 h2) (* h3 
h3) (* h5 h5) j2) (* 4 (* h2 h2) (* h3 h3) (* h5 h5)) (* 64 (* h2 h2) (* h3 h3) 
h5 h6 (* j2 j2 j2 j2)) (* 180 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 169 (* 
h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 60 (* h2 h2) (* h3 h3) h5 h6 j2) (* 7 (* h2
 h2) (* h3 h3) h5 h6) (* 32 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 96
 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 88 (* h2 h2) (* h3 h3) (* h6 h6)
 (* j2 j2)) (* 24 (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 4 (* h2 h2) h3 (* h5 h5 
h5) (* j2 j2 j2 j2)) (* 13 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 15 (* h2 
h2) h3 (* h5 h5 h5) (* j2 j2)) (* 7 (* h2 h2) h3 (* h5 h5 h5) j2) (* (* h2 h2) 
h3 (* h5 h5 h5)) (* 16 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 55 (* h2 h2
) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 69 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 37
 (* h2 h2) h3 (* h5 h5) h6 j2) (* 7 (* h2 h2) h3 (* h5 h5) h6) (* 16 (* h2 h2) 
h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 56 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) 
(* 70 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 36 (* h2 h2) h3 h5 (* h6 h6) j2) 
(* 6 (* h2 h2) h3 h5 (* h6 h6)) (* 4 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 14 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 16 (* h2 h2) h3 (* h6 h6 h6) 
(* j2 j2)) (* 6 (* h2 h2) h3 (* h6 h6 h6) j2) (* (* h2 h2) (* h5 h5 h5) h6 (* j2
 j2 j2 j2)) (* 4 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 6 (* h2 h2) (* h5 h5
 h5) h6 (* j2 j2)) (* 4 (* h2 h2) (* h5 h5 h5) h6 j2) (* (* h2 h2) (* h5 h5 h5) 
h6) (* 2 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h2 h2) (* h5 h5)
 (* h6 h6) (* j2 j2 j2)) (* 12 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 (* 
h2 h2) (* h5 h5) (* h6 h6) j2) (* 2 (* h2 h2) (* h5 h5) (* h6 h6)) (* (* h2 h2) 
h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 6 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2)) (* 4 (* h2 h2) h5 (* h6 h6 h6) j2) (* 
(* h2 h2) h5 (* h6 h6 h6)) (* 64 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 208 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3) (* h5 
h5) (* j2 j2 j2)) (* 148 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 40 h2 (* h3 h3 
h3) (* h5 h5) j2) (* 4 h2 (* h3 h3 h3) (* h5 h5)) (* 128 h2 (* h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2)) (* 448 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 536 h2 (* 
h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 268 h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 56 h2 
(* h3 h3 h3) h5 h6 j2) (* 4 h2 (* h3 h3 h3) h5 h6) (* 64 h2 (* h3 h3 h3) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 240 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 288
 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 116 h2 (* h3 h3 h3) (* h6 h6) (* j2 
j2)) (* 12 h2 (* h3 h3 h3) (* h6 h6) j2) (* 16 h2 (* h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 60 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 86 h2 (* h3 h3
) (* h5 h5 h5) (* j2 j2 j2)) (* 58 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 18 h2
 (* h3 h3) (* h5 h5 h5) j2) (* 2 h2 (* h3 h3) (* h5 h5 h5)) (* 64 h2 (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2
)) (* 392 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 284 h2 (* h3 h3) (* h5 h5) 
h6 (* j2 j2)) (* 96 h2 (* h3 h3) (* h5 h5) h6 j2) (* 12 h2 (* h3 h3) (* h5 h5) 
h6) (* 64 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 268 h2 (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2)) (* 409 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 277
 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 79 h2 (* h3 h3) h5 (* h6 h6) j2) (* 7 
h2 (* h3 h3) h5 (* h6 h6)) (* 16 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 68 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 98 h2 (* h3 h3) (* h6 h6 h6)
 (* j2 j2 j2)) (* 52 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 6 h2 (* h3 h3) (* 
h6 h6 h6) j2) (* 8 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 36 h2 h3 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 64 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 56 h2 h3
 (* h5 h5 h5) h6 (* j2 j2)) (* 24 h2 h3 (* h5 h5 h5) h6 j2) (* 4 h2 h3 (* h5 h5 
h5) h6) (* 16 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 73 h2 h3 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 130 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
112 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 46 h2 h3 (* h5 h5) (* h6 h6) j2) (* 
7 h2 h3 (* h5 h5) (* h6 h6)) (* 8 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
38 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 68 h2 h3 h5 (* h6 h6 h6) (* j2 j2 
j2)) (* 56 h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 20 h2 h3 h5 (* h6 h6 h6) j2) (* 2
 h2 h3 h5 (* h6 h6 h6)) (* h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5 h2
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 10 h2 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 10 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 5 h2 (* h5 h5 h5) (* h6 h6
) j2) (* h2 (* h5 h5 h5) (* h6 h6)) (* h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 5 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10 h2 (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2)) (* 10 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 5 h2 (* h5 h5) 
(* h6 h6 h6) j2) (* h2 (* h5 h5) (* h6 h6 h6)) (* 64 (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 304 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
560 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 508 (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2)) (* 236 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 52 (* h3 h3 h3) (* 
h5 h5) h6 j2) (* 4 (* h3 h3 h3) (* h5 h5) h6) (* 64 (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 320 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
596 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 510 (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2)) (* 202 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 34 (* h3 h3 h3) h5 
(* h6 h6) j2) (* 2 (* h3 h3 h3) h5 (* h6 h6)) (* 16 (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 84 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
174 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 180 (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 96 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 24 (* h3 h3) (* h5 
h5 h5) h6 j2) (* 2 (* h3 h3) (* h5 h5 h5) h6) (* 32 (* h3 h3) (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 168 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 348 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 360 (* h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2)) (* 192 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 
48 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 4 (* h3 h3) (* h5 h5) (* h6 h6)) (* 16 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 88 (* h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 185 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 184 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 86 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2
)) (* 16 (* h3 h3) h5 (* h6 h6 h6) j2) (* (* h3 h3) h5 (* h6 h6 h6)) (* 4 h3 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23 h3 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 53 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 62 h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 38 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 11 
h3 (* h5 h5 h5) (* h6 h6) j2) (* h3 (* h5 h5 h5) (* h6 h6)) (* 4 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 53 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 62 h3 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2)) (* 38 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 11 h3 (* 
h5 h5) (* h6 h6 h6) j2) (* h3 (* h5 h5) (* h6 h6 h6))) 0)))
(check-sat)
(exit)
