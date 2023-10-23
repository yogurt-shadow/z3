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
(set-info :instance |E5E17|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h5 0) (> h6 0) (> j2 0) (= (+ (* 2 
(* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) (* h3 h3) h5 
(* j2 j2 j2 j2)) (* 23 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2 j2)) (* 23 (* h1 h1 h1
) (* h3 h3) h5 (* j2 j2)) (* 11 (* h1 h1 h1) (* h3 h3) h5 j2) (* 2 (* h1 h1 h1) 
(* h3 h3) h5) (* 2 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 12 (* h1 h1 
h1) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 28 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2)) 
(* 32 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2)) (* 18 (* h1 h1 h1) (* h3 h3) h6 j2) 
(* 4 (* h1 h1 h1) (* h3 h3) h6) (* 4 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2 j2)) 
(* 12 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2)) (* 13 (* h1 h1 h1) h3 (* h5 h5) 
(* j2 j2)) (* 6 (* h1 h1 h1) h3 (* h5 h5) j2) (* (* h1 h1 h1) h3 (* h5 h5)) (* 4
 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h3 h5 h6 (* j2 j2 
j2 j2)) (* 53 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2)) (* 55 (* h1 h1 h1) h3 h5 h6 
(* j2 j2)) (* 27 (* h1 h1 h1) h3 h5 h6 j2) (* 5 (* h1 h1 h1) h3 h5 h6) (* 2 (* 
h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h3 (* h6 h6) (* j2
 j2 j2 j2)) (* 20 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2)) (* 20 (* h1 h1 h1) h3 
(* h6 h6) (* j2 j2)) (* 10 (* h1 h1 h1) h3 (* h6 h6) j2) (* 2 (* h1 h1 h1) h3 
(* h6 h6)) (* 4 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 12 (* h1 h1 h1) 
(* h5 h5) h6 (* j2 j2 j2)) (* 13 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* 6 (* h1
 h1 h1) (* h5 h5) h6 j2) (* (* h1 h1 h1) (* h5 h5) h6) (* 2 (* h1 h1 h1) h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16
 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2 j2)) (* 14 (* h1 h1 h1) h5 (* h6 h6) (* j2 
j2)) (* 6 (* h1 h1 h1) h5 (* h6 h6) j2) (* (* h1 h1 h1) h5 (* h6 h6)) (* (* h1 
h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h2 (* h3 h3) h5 (* j2
 j2 j2 j2 j2)) (* 52 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2)) (* 94 (* h1 h1) 
h2 (* h3 h3) h5 (* j2 j2 j2)) (* 85 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2)) (* 37 
(* h1 h1) h2 (* h3 h3) h5 j2) (* 6 (* h1 h1) h2 (* h3 h3) h5) (* 6 (* h1 h1) h2 
(* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2)
) (* 84 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2)) (* 96 (* h1 h1) h2 (* h3 h3) h6 
(* j2 j2)) (* 54 (* h1 h1) h2 (* h3 h3) h6 j2) (* 12 (* h1 h1) h2 (* h3 h3) h6) 
(* 4 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 26 (* h1 h1) h2 h3 (* h5 
h5) (* j2 j2 j2 j2)) (* 54 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2 j2)) (* 49 (* h1 
h1) h2 h3 (* h5 h5) (* j2 j2)) (* 20 (* h1 h1) h2 h3 (* h5 h5) j2) (* 3 (* h1 h1
) h2 h3 (* h5 h5)) (* 2 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 23 (* h1
 h1) h2 h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 93 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2)
) (* 176 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2)) (* 170 (* h1 h1) h2 h3 h5 h6 (* j2 
j2)) (* 81 (* h1 h1) h2 h3 h5 h6 j2) (* 15 (* h1 h1) h2 h3 h5 h6) (* 6 (* h1 h1)
 h2 h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2
 j2)) (* 60 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2)) (* 60 (* h1 h1) h2 h3 (* h6 
h6) (* j2 j2)) (* 30 (* h1 h1) h2 h3 (* h6 h6) j2) (* 6 (* h1 h1) h2 h3 (* h6 h6
)) (* 4 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22 (* h1 h1) h2 (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 44 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2)) (* 41 (* 
h1 h1) h2 (* h5 h5) h6 (* j2 j2)) (* 18 (* h1 h1) h2 (* h5 h5) h6 j2) (* 3 (* h1
 h1) h2 (* h5 h5) h6) (* (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 10 
(* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 33 (* h1 h1) h2 h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 52 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2)) (* 43 (* h1 h1) 
h2 h5 (* h6 h6) (* j2 j2)) (* 18 (* h1 h1) h2 h5 (* h6 h6) j2) (* 3 (* h1 h1) h2
 h5 (* h6 h6)) (* 2 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 13 (* h1 h1
) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2))
 (* 37 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2)) (* 20 (* h1 h1) (* h3 h3 h3) h5 j2) 
(* 4 (* h1 h1) (* h3 h3 h3) h5) (* 2 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2
)) (* 14 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 38 (* h1 h1) (* h3 h3 h3)
 h6 (* j2 j2 j2)) (* 50 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2)) (* 32 (* h1 h1) (* 
h3 h3 h3) h6 j2) (* 8 (* h1 h1) (* h3 h3 h3) h6) (* 4 (* h1 h1) (* h3 h3) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 22 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 
48 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 49 (* h1 h1) (* h3 h3) (* h5 
h5) (* j2 j2)) (* 23 (* h1 h1) (* h3 h3) (* h5 h5) j2) (* 4 (* h1 h1) (* h3 h3) 
(* h5 h5)) (* 11 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1) 
(* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 145 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2)) 
(* 158 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2)) (* 82 (* h1 h1) (* h3 h3) h5 h6 j2) 
(* 16 (* h1 h1) (* h3 h3) h5 h6) (* 4 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 24 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 56 (* h1 h1) (* 
h3 h3) (* h6 h6) (* j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) 
(* 36 (* h1 h1) (* h3 h3) (* h6 h6) j2) (* 8 (* h1 h1) (* h3 h3) (* h6 h6)) (* 4
 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 12 (* h1 h1) h3 (* h5 h5 h5) (* 
j2 j2 j2)) (* 13 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2)) (* 6 (* h1 h1) h3 (* h5 h5
 h5) j2) (* (* h1 h1) h3 (* h5 h5 h5)) (* 8 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 46 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 99 (* h1 h1) h3 
(* h5 h5) h6 (* j2 j2 j2)) (* 99 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2)) (* 46 (* 
h1 h1) h3 (* h5 h5) h6 j2) (* 8 (* h1 h1) h3 (* h5 h5) h6) (* 11 (* h1 h1) h3 h5
 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 55 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 108 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 104 (* h1 h1) h3 h5 (* h6 h6) 
(* j2 j2)) (* 49 (* h1 h1) h3 h5 (* h6 h6) j2) (* 9 (* h1 h1) h3 h5 (* h6 h6)) 
(* 2 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h3 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 20 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 20 (* h1 
h1) h3 (* h6 h6 h6) (* j2 j2)) (* 10 (* h1 h1) h3 (* h6 h6 h6) j2) (* 2 (* h1 h1
) h3 (* h6 h6 h6)) (* 4 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12 (* h1 
h1) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 13 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2)) (* 
6 (* h1 h1) (* h5 h5 h5) h6 j2) (* (* h1 h1) (* h5 h5 h5) h6) (* 4 (* h1 h1) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 32 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 28 (* h1 h1) (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 12 (* h1 h1) (* h5 h5) (* h6 h6) j2) (* 2 (* h1 
h1) (* h5 h5) (* h6 h6)) (* 2 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 9
 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) h5 (* h6 h6 h6) (* 
j2 j2 j2)) (* 14 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2)) (* 6 (* h1 h1) h5 (* h6 h6
 h6) j2) (* (* h1 h1) h5 (* h6 h6 h6)) (* 2 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 
j2 j2 j2 j2)) (* 20 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 71 h1 (* h2
 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 119 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2)
) (* 101 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2)) (* 41 h1 (* h2 h2) (* h3 h3) h5 j2
) (* 6 h1 (* h2 h2) (* h3 h3) h5) (* 6 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 
j2)) (* 36 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 84 h1 (* h2 h2) (* h3 
h3) h6 (* j2 j2 j2)) (* 96 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2)) (* 54 h1 (* h2 
h2) (* h3 h3) h6 j2) (* 12 h1 (* h2 h2) (* h3 h3) h6) (* h1 (* h2 h2) h3 (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) 
(* 45 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 74 h1 (* h2 h2) h3 (* h5 h5)
 (* j2 j2 j2)) (* 59 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2)) (* 22 h1 (* h2 h2) h3 
(* h5 h5) j2) (* 3 h1 (* h2 h2) h3 (* h5 h5)) (* 4 h1 (* h2 h2) h3 h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 34 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 114 h1 (* h2
 h2) h3 h5 h6 (* j2 j2 j2 j2)) (* 193 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 175
 h1 (* h2 h2) h3 h5 h6 (* j2 j2)) (* 81 h1 (* h2 h2) h3 h5 h6 j2) (* 15 h1 (* h2
 h2) h3 h5 h6) (* 6 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 h1 (* h2
 h2) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 60 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2))
 (* 60 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2)) (* 30 h1 (* h2 h2) h3 (* h6 h6) j2) 
(* 6 h1 (* h2 h2) h3 (* h6 h6)) (* h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 10 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 33 h1 (* h2 h2) (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 52 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 43 
h1 (* h2 h2) (* h5 h5) h6 (* j2 j2)) (* 18 h1 (* h2 h2) (* h5 h5) h6 j2) (* 3 h1
 (* h2 h2) (* h5 h5) h6) (* 2 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 14 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39 h1 (* h2 h2) h5 (* h6 
h6) (* j2 j2 j2 j2)) (* 56 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 44 h1 (* 
h2 h2) h5 (* h6 h6) (* j2 j2)) (* 18 h1 (* h2 h2) h5 (* h6 h6) j2) (* 3 h1 (* h2
 h2) h5 (* h6 h6)) (* h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 12 h1 h2 
(* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 51 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2))
 (* 102 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2)) (* 102 h1 h2 (* h3 h3 h3) h5 (* j2 
j2)) (* 48 h1 h2 (* h3 h3 h3) h5 j2) (* 8 h1 h2 (* h3 h3 h3) h5) (* 4 h1 h2 (* 
h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 28 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2 j2)) 
(* 76 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2)) (* 100 h1 h2 (* h3 h3 h3) h6 (* j2 j2)
) (* 64 h1 h2 (* h3 h3 h3) h6 j2) (* 16 h1 h2 (* h3 h3 h3) h6) (* 2 h1 h2 (* h3 
h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 22 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 81 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 142 h1 h2 (* h3 h3)
 (* h5 h5) (* j2 j2 j2)) (* 125 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2)) (* 52 h1 h2
 (* h3 h3) (* h5 h5) j2) (* 8 h1 h2 (* h3 h3) (* h5 h5)) (* 3 h1 h2 (* h3 h3) h5
 h6 (* j2 j2 j2 j2 j2 j2)) (* 38 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 
157 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 308 h1 h2 (* h3 h3) h5 h6 (* j2 j2
 j2)) (* 314 h1 h2 (* h3 h3) h5 h6 (* j2 j2)) (* 160 h1 h2 (* h3 h3) h5 h6 j2) 
(* 32 h1 h2 (* h3 h3) h5 h6) (* 8 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 48 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 112 h1 h2 (* h3 h3) (* h6 h6
) (* j2 j2 j2)) (* 128 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2)) (* 72 h1 h2 (* h3 h3
) (* h6 h6) j2) (* 16 h1 h2 (* h3 h3) (* h6 h6)) (* 4 h1 h2 h3 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 22 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 42 h1 h2 h3 (* 
h5 h5 h5) (* j2 j2 j2)) (* 36 h1 h2 h3 (* h5 h5 h5) (* j2 j2)) (* 14 h1 h2 h3 
(* h5 h5 h5) j2) (* 2 h1 h2 h3 (* h5 h5 h5)) (* 4 h1 h2 h3 (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 37 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 129 h1 h2 h3 
(* h5 h5) h6 (* j2 j2 j2 j2)) (* 221 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2)) (* 199 
h1 h2 h3 (* h5 h5) h6 (* j2 j2)) (* 90 h1 h2 h3 (* h5 h5) h6 j2) (* 16 h1 h2 h3 
(* h5 h5) h6) (* 3 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 34 h1 h2 h3 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 126 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 222 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2)) (* 205 h1 h2 h3 h5 (* h6 h6) (* j2 j2
)) (* 96 h1 h2 h3 h5 (* h6 h6) j2) (* 18 h1 h2 h3 h5 (* h6 h6)) (* 4 h1 h2 h3 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 20 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 40 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2)) (* 40 h1 h2 h3 (* h6 h6 h6) (* j2 j2))
 (* 20 h1 h2 h3 (* h6 h6 h6) j2) (* 4 h1 h2 h3 (* h6 h6 h6)) (* 4 h1 h2 (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 18 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 32 
h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 28 h1 h2 (* h5 h5 h5) h6 (* j2 j2)) (* 12
 h1 h2 (* h5 h5 h5) h6 j2) (* 2 h1 h2 (* h5 h5 h5) h6) (* 2 h1 h2 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 48 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 72 h1 h2 (* h5 h5) (* h6 
h6) (* j2 j2 j2)) (* 58 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2)) (* 24 h1 h2 (* h5 
h5) (* h6 h6) j2) (* 4 h1 h2 (* h5 h5) (* h6 h6)) (* h1 h2 h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 8 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 h1 h2 h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 36 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 29 h1
 h2 h5 (* h6 h6 h6) (* j2 j2)) (* 12 h1 h2 h5 (* h6 h6 h6) j2) (* 2 h1 h2 h5 (* 
h6 h6 h6)) (* 2 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 13 h1 (* h3 h3 
h3) (* h5 h5) (* j2 j2 j2 j2)) (* 30 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
30 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 13 h1 (* h3 h3 h3) (* h5 h5) j2) (* 2
 h1 (* h3 h3 h3) (* h5 h5)) (* 3 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 24
 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 67 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2)
) (* 82 h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 44 h1 (* h3 h3 h3) h5 h6 j2) (* 8 h1
 (* h3 h3 h3) h5 h6) (* 4 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 20 h1 
(* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 36 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2)) 
(* 28 h1 (* h3 h3 h3) (* h6 h6) j2) (* 8 h1 (* h3 h3 h3) (* h6 h6)) (* 2 h1 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 11 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2
 j2 j2)) (* 21 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 18 h1 (* h3 h3) (* h5 
h5 h5) (* j2 j2)) (* 7 h1 (* h3 h3) (* h5 h5 h5) j2) (* h1 (* h3 h3) (* h5 h5 h5
)) (* 10 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 59 h1 (* h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2)) (* 128 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 126 h1
 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 56 h1 (* h3 h3) (* h5 h5) h6 j2) (* 9 h1 
(* h3 h3) (* h5 h5) h6) (* 6 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 44
 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 114 h1 (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2)) (* 136 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 76 h1 (* h3 h3) h5 (* 
h6 h6) j2) (* 16 h1 (* h3 h3) h5 (* h6 h6)) (* 4 h1 (* h3 h3) (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 24 h1 (* h3 h3) (* 
h6 h6 h6) (* j2 j2)) (* 16 h1 (* h3 h3) (* h6 h6 h6) j2) (* 4 h1 (* h3 h3) (* h6
 h6 h6)) (* 4 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 22 h1 h3 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2)) (* 42 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 36 h1 h3 (* h5
 h5 h5) h6 (* j2 j2)) (* 14 h1 h3 (* h5 h5 h5) h6 j2) (* 2 h1 h3 (* h5 h5 h5) h6
) (* 10 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 51 h1 h3 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2)) (* 101 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 97 h1 
h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 45 h1 h3 (* h5 h5) (* h6 h6) j2) (* 8 h1 h3
 (* h5 h5) (* h6 h6)) (* 3 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18 h1 h3
 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 40 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 
42 h1 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 21 h1 h3 h5 (* h6 h6 h6) j2) (* 4 h1 h3 
h5 (* h6 h6 h6)) (* 2 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 9 h1 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
)) (* 14 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 h1 (* h5 h5 h5) (* h6 h6) j2)
 (* h1 (* h5 h5 h5) (* h6 h6)) (* 2 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* 9 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2)) (* 14 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 6 h1 (* h5 h5) (* 
h6 h6 h6) j2) (* h1 (* h5 h5) (* h6 h6 h6)) (* (* h2 h2 h2) (* h3 h3) h5 (* j2 
j2 j2 j2 j2 j2)) (* 9 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 30 (* h2 
h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2
)) (* 39 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2)) (* 15 (* h2 h2 h2) (* h3 h3) h5 j2
) (* 2 (* h2 h2 h2) (* h3 h3) h5) (* 2 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 
j2)) (* 12 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2) (* h3 
h3) h6 (* j2 j2 j2)) (* 32 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 18 (* h2 h2 
h2) (* h3 h3) h6 j2) (* 4 (* h2 h2 h2) (* h3 h3) h6) (* (* h2 h2 h2) h3 (* h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
23 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 32 (* h2 h2 h2) h3 (* h5 h5) 
(* j2 j2 j2)) (* 23 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2)) (* 8 (* h2 h2 h2) h3 
(* h5 h5) j2) (* (* h2 h2 h2) h3 (* h5 h5)) (* 2 (* h2 h2 h2) h3 h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 15 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 45 (* h2 h2 h2)
 h3 h5 h6 (* j2 j2 j2 j2)) (* 70 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 60 (* h2
 h2 h2) h3 h5 h6 (* j2 j2)) (* 27 (* h2 h2 h2) h3 h5 h6 j2) (* 5 (* h2 h2 h2) h3
 h5 h6) (* 2 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2 h2) h3
 (* h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 20 
(* h2 h2 h2) h3 (* h6 h6) (* j2 j2)) (* 10 (* h2 h2 h2) h3 (* h6 h6) j2) (* 2 
(* h2 h2 h2) h3 (* h6 h6)) (* (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 6 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2 h2) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 20 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 15 (* h2 h2
 h2) (* h5 h5) h6 (* j2 j2)) (* 6 (* h2 h2 h2) (* h5 h5) h6 j2) (* (* h2 h2 h2) 
(* h5 h5) h6) (* (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 
h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2
 j2)) (* 20 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 15 (* h2 h2 h2) h5 (* h6 
h6) (* j2 j2)) (* 6 (* h2 h2 h2) h5 (* h6 h6) j2) (* (* h2 h2 h2) h5 (* h6 h6)) 
(* (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 10 (* h2 h2) (* h3 h3 h3)
 h5 (* j2 j2 j2 j2 j2)) (* 38 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 70 
(* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 65 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2
)) (* 28 (* h2 h2) (* h3 h3 h3) h5 j2) (* 4 (* h2 h2) (* h3 h3 h3) h5) (* 2 (* 
h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 14 (* h2 h2) (* h3 h3 h3) h6 (* j2
 j2 j2 j2)) (* 38 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 50 (* h2 h2) (* h3 
h3 h3) h6 (* j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3) h6 j2) (* 8 (* h2 h2) (* h3 h3
 h3) h6) (* 2 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 17 (* h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 54 (* h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2)) (* 86 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 72 (* h2 
h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 29 (* h2 h2) (* h3 h3) (* h5 h5) j2) (* 4 
(* h2 h2) (* h3 h3) (* h5 h5)) (* 3 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 27 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 93 (* h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2)) (* 163 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 156
 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 78 (* h2 h2) (* h3 h3) h5 h6 j2) (* 16 
(* h2 h2) (* h3 h3) h5 h6) (* 4 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 24 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 56 (* h2 h2) (* h3 h3)
 (* h6 h6) (* j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2)) (* 36 
(* h2 h2) (* h3 h3) (* h6 h6) j2) (* 8 (* h2 h2) (* h3 h3) (* h6 h6)) (* (* h2 
h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) h3 (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 23 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 32 (* h2 h2) 
h3 (* h5 h5 h5) (* j2 j2 j2)) (* 23 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2)) (* 8 
(* h2 h2) h3 (* h5 h5 h5) j2) (* (* h2 h2) h3 (* h5 h5 h5)) (* 4 (* h2 h2) h3 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 80 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 120 (* h2 h2) h3 (* 
h5 h5) h6 (* j2 j2 j2)) (* 100 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 44 (* h2 
h2) h3 (* h5 h5) h6 j2) (* 8 (* h2 h2) h3 (* h5 h5) h6) (* 3 (* h2 h2) h3 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 23 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 71 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 114 (* h2 h2) h3 h5 (* h6 
h6) (* j2 j2 j2)) (* 101 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2)) (* 47 (* h2 h2) h3
 h5 (* h6 h6) j2) (* 9 (* h2 h2) h3 h5 (* h6 h6)) (* 2 (* h2 h2) h3 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2)) (* 10 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* 
h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 20 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) 
(* 10 (* h2 h2) h3 (* h6 h6 h6) j2) (* 2 (* h2 h2) h3 (* h6 h6 h6)) (* (* h2 h2)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 15 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 20 (* h2 h2) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 15 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 6 (* h2
 h2) (* h5 h5 h5) h6 j2) (* (* h2 h2) (* h5 h5 h5) h6) (* 2 (* h2 h2) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 30 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40 (* h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2))
 (* 12 (* h2 h2) (* h5 h5) (* h6 h6) j2) (* 2 (* h2 h2) (* h5 h5) (* h6 h6)) (* 
(* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 15 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 (* h2
 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 15 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2)) 
(* 6 (* h2 h2) h5 (* h6 h6 h6) j2) (* (* h2 h2) h5 (* h6 h6 h6)) (* h2 (* h3 h3 
h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2
 j2 j2)) (* 37 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 63 h2 (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2)) (* 50 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 17 h2 (* 
h3 h3 h3) (* h5 h5) j2) (* 2 h2 (* h3 h3 h3) (* h5 h5)) (* 3 h2 (* h3 h3 h3) h5 
h6 (* j2 j2 j2 j2 j2)) (* 24 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 67 h2 (* 
h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 82 h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 44 h2 
(* h3 h3 h3) h5 h6 j2) (* 8 h2 (* h3 h3 h3) h5 h6) (* 4 h2 (* h3 h3 h3) (* h6 h6
) (* j2 j2 j2 j2)) (* 20 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 36 h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2)) (* 28 h2 (* h3 h3 h3) (* h6 h6) j2) (* 8 h2 (* h3 h3
 h3) (* h6 h6)) (* h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9 h2 (* 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 29 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2
 j2 j2)) (* 42 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 29 h2 (* h3 h3) (* h5 
h5 h5) (* j2 j2)) (* 9 h2 (* h3 h3) (* h5 h5 h5) j2) (* h2 (* h3 h3) (* h5 h5 h5
)) (* 3 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 h2 (* h3 h3) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 93 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 157 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 137 h2 (* h3 h3) (* h5 h5) h6 
(* j2 j2)) (* 58 h2 (* h3 h3) (* h5 h5) h6 j2) (* 9 h2 (* h3 h3) (* h5 h5) h6) 
(* 6 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 42 h2 (* h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2)) (* 106 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 126 h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 72 h2 (* h3 h3) h5 (* h6 h6) j2) (* 16 h2 
(* h3 h3) h5 (* h6 h6)) (* 4 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h2
 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 24 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2))
 (* 16 h2 (* h3 h3) (* h6 h6 h6) j2) (* 4 h2 (* h3 h3) (* h6 h6 h6)) (* 2 h2 h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 14 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 38 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 52 h2 h3 (* h5 h5 h5) h6
 (* j2 j2 j2)) (* 38 h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 14 h2 h3 (* h5 h5 h5) 
h6 j2) (* 2 h2 h3 (* h5 h5 h5) h6) (* 3 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 23 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 70 h2 h3 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 110 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 95 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 43 h2 h3 (* h5 h5) (* h6 h6) j2) 
(* 8 h2 h3 (* h5 h5) (* h6 h6)) (* 3 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 16 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 34 h2 h3 h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 36 h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 19 h2 h3 h5 (* h6 h6 h6) j2) 
(* 4 h2 h3 h5 (* h6 h6 h6)) (* h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 6 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 20 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 15 h2 (* 
h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 h2 (* h5 h5 h5) (* h6 h6) j2) (* h2 (* h5 h5
 h5) (* h6 h6)) (* h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h2 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2)) (* 20 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 15 h2 (* h5 h5) (* h6 
h6 h6) (* j2 j2)) (* 6 h2 (* h5 h5) (* h6 h6 h6) j2) (* h2 (* h5 h5) (* h6 h6 h6
)) (* (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6 (* h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 12 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 9 (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2)) (* 2 (* h3 h3 h3) (* h5 h5) h6 j2) (* 2 (* h3 h3 h3)
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 8 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 
10 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 4 (* h3 h3 h3) h5 (* h6 h6) j2) (* 
(* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5 (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 8 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 5 (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2)) (* (* h3 h3) (* h5 h5 h5) h6 j2) (* 2 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 11 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 21 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 17 (* h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2)) (* 5 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 2 (* h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 6 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 2 (* h3 h3) h5 (* h6 h6 h6) j2) (* h3 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2 j2)) (* 6 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 h3 (* h5 h5 h5) (* 
h6 h6) (* j2 j2)) (* h3 (* h5 h5 h5) (* h6 h6) j2) (* h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 4 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 h3 (* 
h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 4 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 
h3 (* h5 h5) (* h6 h6 h6) j2)) 0)))
(check-sat)
(exit)
