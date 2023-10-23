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
(set-info :instance |E6E17|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h5 0) (> h6 0) (> j2 0) (= (+ (* 6 
(* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 46 (* h1 h1 h1) (* h3 h3) h6 
(* j2 j2 j2 j2)) (* 118 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2 j2)) (* 138 (* h1 h1 
h1) (* h3 h3) h6 (* j2 j2)) (* 76 (* h1 h1 h1) (* h3 h3) h6 j2) (* 16 (* h1 h1 
h1) (* h3 h3) h6) (* 6 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h1
 h1 h1) h3 (* h6 h6) (* j2 j2 j2 j2)) (* 52 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2 
j2)) (* 48 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2)) (* 22 (* h1 h1 h1) h3 (* h6 h6) 
j2) (* 4 (* h1 h1 h1) h3 (* h6 h6)) (* (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2 
j2 j2)) (* 12 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 54 (* h1 h1) h2 
(* h3 h3) h5 (* j2 j2 j2 j2)) (* 116 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2)) (* 
129 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2)) (* 72 (* h1 h1) h2 (* h3 h3) h5 j2) (* 
16 (* h1 h1) h2 (* h3 h3) h5) (* 18 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2 j2)
) (* 138 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2 j2)) (* 354 (* h1 h1) h2 (* h3 h3
) h6 (* j2 j2 j2)) (* 414 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2)) (* 228 (* h1 h1) 
h2 (* h3 h3) h6 j2) (* 48 (* h1 h1) h2 (* h3 h3) h6) (* 2 (* h1 h1) h2 h3 h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 60 (* 
h1 h1) h2 h3 h5 h6 (* j2 j2 j2 j2)) (* 100 (* h1 h1) h2 h3 h5 h6 (* j2 j2 j2)) 
(* 90 (* h1 h1) h2 h3 h5 h6 (* j2 j2)) (* 42 (* h1 h1) h2 h3 h5 h6 j2) (* 8 (* 
h1 h1) h2 h3 h5 h6) (* 18 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 84 
(* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2 j2)) (* 156 (* h1 h1) h2 h3 (* h6 h6) (* 
j2 j2 j2)) (* 144 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2)) (* 66 (* h1 h1) h2 h3 (* 
h6 h6) j2) (* 12 (* h1 h1) h2 h3 (* h6 h6)) (* (* h1 h1) h2 h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h1 
h1) h2 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 20 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2
)) (* 15 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2)) (* 6 (* h1 h1) h2 h5 (* h6 h6) j2)
 (* (* h1 h1) h2 h5 (* h6 h6)) (* 6 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)
) (* 64 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 238 (* h1 h1) (* h3 h3 h3)
 h6 (* j2 j2 j2)) (* 372 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2)) (* 256 (* h1 h1) 
(* h3 h3 h3) h6 j2) (* 64 (* h1 h1) (* h3 h3 h3) h6) (* 18 (* h1 h1) (* h3 h3) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 138 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 
354 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 414 (* h1 h1) (* h3 h3) h5 h6 (* 
j2 j2)) (* 228 (* h1 h1) (* h3 h3) h5 h6 j2) (* 48 (* h1 h1) (* h3 h3) h5 h6) 
(* 12 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 92 (* h1 h1) (* h3 h3
) (* h6 h6) (* j2 j2 j2 j2)) (* 236 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2)) 
(* 276 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) (* 152 (* h1 h1) (* h3 h3) (* h6
 h6) j2) (* 32 (* h1 h1) (* h3 h3) (* h6 h6)) (* 18 (* h1 h1) h3 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 84 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 156 (* 
h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 144 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2))
 (* 66 (* h1 h1) h3 h5 (* h6 h6) j2) (* 12 (* h1 h1) h3 h5 (* h6 h6)) (* 6 (* h1
 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h1 h1) h3 (* h6 h6 h6) (* j2 
j2 j2 j2)) (* 52 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h1 h1) h3 (* 
h6 h6 h6) (* j2 j2)) (* 22 (* h1 h1) h3 (* h6 h6 h6) j2) (* 4 (* h1 h1) h3 (* h6
 h6 h6)) (* 2 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2
) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 108 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2 
j2)) (* 232 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 258 h1 (* h2 h2) (* h3 h3
) h5 (* j2 j2)) (* 144 h1 (* h2 h2) (* h3 h3) h5 j2) (* 32 h1 (* h2 h2) (* h3 h3
) h5) (* 18 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 138 h1 (* h2 h2) 
(* h3 h3) h6 (* j2 j2 j2 j2)) (* 354 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 
414 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2)) (* 228 h1 (* h2 h2) (* h3 h3) h6 j2) 
(* 48 h1 (* h2 h2) (* h3 h3) h6) (* h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 9 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2) h3 
(* h5 h5) (* j2 j2 j2 j2)) (* 50 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 45 
h1 (* h2 h2) h3 (* h5 h5) (* j2 j2)) (* 21 h1 (* h2 h2) h3 (* h5 h5) j2) (* 4 h1
 (* h2 h2) h3 (* h5 h5)) (* 4 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 36
 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 120 h1 (* h2 h2) h3 h5 h6 (* j2 j2
 j2 j2)) (* 200 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 180 h1 (* h2 h2) h3 h5 h6
 (* j2 j2)) (* 84 h1 (* h2 h2) h3 h5 h6 j2) (* 16 h1 (* h2 h2) h3 h5 h6) (* 18 
h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 84 h1 (* h2 h2) h3 (* h6 h6) 
(* j2 j2 j2 j2)) (* 156 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 144 h1 (* h2 
h2) h3 (* h6 h6) (* j2 j2)) (* 66 h1 (* h2 h2) h3 (* h6 h6) j2) (* 12 h1 (* h2 
h2) h3 (* h6 h6)) (* h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 h1 
(* h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 h1 (* h2 h2) (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 20 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 15 h1 (* h2 h2) (* 
h5 h5) h6 (* j2 j2)) (* 6 h1 (* h2 h2) (* h5 h5) h6 j2) (* h1 (* h2 h2) (* h5 h5
) h6) (* 2 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)
) (* 40 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 30 h1 (* h2 h2) h5 (* h6 h6) 
(* j2 j2)) (* 12 h1 (* h2 h2) h5 (* h6 h6) j2) (* 2 h1 (* h2 h2) h5 (* h6 h6)) 
(* h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 (* h3 h3 h3) h5 (* 
j2 j2 j2 j2 j2)) (* 87 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 245 h1 h2 (* h3
 h3 h3) h5 (* j2 j2 j2)) (* 348 h1 h2 (* h3 h3 h3) h5 (* j2 j2)) (* 240 h1 h2 
(* h3 h3 h3) h5 j2) (* 64 h1 h2 (* h3 h3 h3) h5) (* 12 h1 h2 (* h3 h3 h3) h6 (* 
j2 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 476 h1 h2 (* 
h3 h3 h3) h6 (* j2 j2 j2)) (* 744 h1 h2 (* h3 h3 h3) h6 (* j2 j2)) (* 512 h1 h2 
(* h3 h3 h3) h6 j2) (* 128 h1 h2 (* h3 h3 h3) h6) (* 2 h1 h2 (* h3 h3) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2)) (* 24 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 
108 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 232 h1 h2 (* h3 h3) (* h5 h5) 
(* j2 j2 j2)) (* 258 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2)) (* 144 h1 h2 (* h3 h3)
 (* h5 h5) j2) (* 32 h1 h2 (* h3 h3) (* h5 h5)) (* 3 h1 h2 (* h3 h3) h5 h6 (* j2
 j2 j2 j2 j2 j2)) (* 60 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 346 h1 h2 
(* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 820 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2)) (* 
939 h1 h2 (* h3 h3) h5 h6 (* j2 j2)) (* 520 h1 h2 (* h3 h3) h5 h6 j2) (* 112 h1 
h2 (* h3 h3) h5 h6) (* 24 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 184 
h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 472 h1 h2 (* h3 h3) (* h6 h6) (* 
j2 j2 j2)) (* 552 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2)) (* 304 h1 h2 (* h3 h3) 
(* h6 h6) j2) (* 64 h1 h2 (* h3 h3) (* h6 h6)) (* 4 h1 h2 h3 (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 36 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 120 h1 h2 h3
 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 200 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2)) (* 180
 h1 h2 h3 (* h5 h5) h6 (* j2 j2)) (* 84 h1 h2 h3 (* h5 h5) h6 j2) (* 16 h1 h2 h3
 (* h5 h5) h6) (* 3 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 51 h1 h2 h3 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 202 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 358 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2)) (* 327 h1 h2 h3 h5 (* h6 h6) (* j2 j2
)) (* 151 h1 h2 h3 h5 (* h6 h6) j2) (* 28 h1 h2 h3 h5 (* h6 h6)) (* 12 h1 h2 h3 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 104 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2)) (* 96 h1 h2 h3 (* h6 h6 h6) (* j2 j2)
) (* 44 h1 h2 h3 (* h6 h6 h6) j2) (* 8 h1 h2 h3 (* h6 h6 h6)) (* 2 h1 h2 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 30 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 40 h1 h2 (* h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 30 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2)) (* 12 h1 h2 
(* h5 h5) (* h6 h6) j2) (* 2 h1 h2 (* h5 h5) (* h6 h6)) (* h1 h2 h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 6 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h1 
h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 15 h1 h2 h5 (* h6 h6 h6) (* j2 j2)) (* 6 h1 h2 h5 (* h6 h6 h6) j2) (* h1 h2 
h5 (* h6 h6 h6)) (* 12 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 128 h1 (* h3
 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 476 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 744
 h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 512 h1 (* h3 h3 h3) h5 h6 j2) (* 128 h1 (* 
h3 h3 h3) h5 h6) (* 36 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 228 h1 (* 
h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 400 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2)) 
(* 272 h1 (* h3 h3 h3) (* h6 h6) j2) (* 64 h1 (* h3 h3 h3) (* h6 h6)) (* 18 h1 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 138 h1 (* h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2)) (* 354 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 414 h1 (* h3 h3)
 (* h5 h5) h6 (* j2 j2)) (* 228 h1 (* h3 h3) (* h5 h5) h6 j2) (* 48 h1 (* h3 h3)
 (* h5 h5) h6) (* 24 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 184 h1 (* 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 472 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 
j2)) (* 552 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 304 h1 (* h3 h3) h5 (* h6 h6
) j2) (* 64 h1 (* h3 h3) h5 (* h6 h6)) (* 36 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 120 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2)) (* 148 h1 (* h3 h3) (* h6
 h6 h6) (* j2 j2)) (* 80 h1 (* h3 h3) (* h6 h6 h6) j2) (* 16 h1 (* h3 h3) (* h6 
h6 h6)) (* 18 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 84 h1 h3 (* h5 h5
) (* h6 h6) (* j2 j2 j2 j2)) (* 156 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 
144 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 66 h1 h3 (* h5 h5) (* h6 h6) j2) (* 
12 h1 h3 (* h5 h5) (* h6 h6)) (* 12 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 56 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 104 h1 h3 h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 96 h1 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 44 h1 h3 h5 (* h6 h6 h6) j2) 
(* 8 h1 h3 h5 (* h6 h6 h6)) (* (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 12 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 54 (* h2 h2 h2) (* h3 h3)
 h5 (* j2 j2 j2 j2)) (* 116 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 129 (* h2
 h2 h2) (* h3 h3) h5 (* j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) h5 j2) (* 16 (* h2 
h2 h2) (* h3 h3) h5) (* 6 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 46 
(* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 j2)) (* 118 (* h2 h2 h2) (* h3 h3) h6 (* 
j2 j2 j2)) (* 138 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2)) (* 76 (* h2 h2 h2) (* h3 
h3) h6 j2) (* 16 (* h2 h2 h2) (* h3 h3) h6) (* (* h2 h2 h2) h3 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 9 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 30 (* h2 
h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2)) (* 50 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2
)) (* 45 (* h2 h2 h2) h3 (* h5 h5) (* j2 j2)) (* 21 (* h2 h2 h2) h3 (* h5 h5) j2
) (* 4 (* h2 h2 h2) h3 (* h5 h5)) (* 2 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 18 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 60 (* h2 h2 h2) h3 h5 h6
 (* j2 j2 j2 j2)) (* 100 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 90 (* h2 h2 h2) 
h3 h5 h6 (* j2 j2)) (* 42 (* h2 h2 h2) h3 h5 h6 j2) (* 8 (* h2 h2 h2) h3 h5 h6) 
(* 6 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h2 h2 h2) h3 (* h6 
h6) (* j2 j2 j2 j2)) (* 52 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 48 (* h2 
h2 h2) h3 (* h6 h6) (* j2 j2)) (* 22 (* h2 h2 h2) h3 (* h6 h6) j2) (* 4 (* h2 h2
 h2) h3 (* h6 h6)) (* (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* 
h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2 h2) (* h5 h5) h6 (* j2
 j2 j2 j2)) (* 20 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2)) (* 15 (* h2 h2 h2) (* 
h5 h5) h6 (* j2 j2)) (* 6 (* h2 h2 h2) (* h5 h5) h6 j2) (* (* h2 h2 h2) (* h5 h5
) h6) (* (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2)) 
(* 20 (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 15 (* h2 h2 h2) h5 (* h6 h6) 
(* j2 j2)) (* 6 (* h2 h2 h2) h5 (* h6 h6) j2) (* (* h2 h2 h2) h5 (* h6 h6)) (* 
(* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 15 (* h2 h2) (* h3 h3 h3) h5
 (* j2 j2 j2 j2 j2)) (* 87 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 245 (* 
h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 348 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2))
 (* 240 (* h2 h2) (* h3 h3 h3) h5 j2) (* 64 (* h2 h2) (* h3 h3 h3) h5) (* 6 (* 
h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) h6 (* j2
 j2 j2 j2)) (* 238 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 372 (* h2 h2) (* 
h3 h3 h3) h6 (* j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3) h6 j2) (* 64 (* h2 h2) (* 
h3 h3 h3) h6) (* 2 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24 
(* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 108 (* h2 h2) (* h3 h3) (* 
h5 h5) (* j2 j2 j2 j2)) (* 232 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 
258 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 144 (* h2 h2) (* h3 h3) (* h5 h5
) j2) (* 32 (* h2 h2) (* h3 h3) (* h5 h5)) (* 3 (* h2 h2) (* h3 h3) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 42 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 208 (* 
h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 466 (* h2 h2) (* h3 h3) h5 h6 (* j2 
j2 j2)) (* 525 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 292 (* h2 h2) (* h3 h3) 
h5 h6 j2) (* 64 (* h2 h2) (* h3 h3) h5 h6) (* 12 (* h2 h2) (* h3 h3) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 92 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 236 
(* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 276 (* h2 h2) (* h3 h3) (* h6 h6)
 (* j2 j2)) (* 152 (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 32 (* h2 h2) (* h3 h3) 
(* h6 h6)) (* (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 9 (* h2 h2) h3
 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 30 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2
)) (* 50 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 45 (* h2 h2) h3 (* h5 h5 h5)
 (* j2 j2)) (* 21 (* h2 h2) h3 (* h5 h5 h5) j2) (* 4 (* h2 h2) h3 (* h5 h5 h5)) 
(* 4 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2) h3 (* h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 120 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
200 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2)) (* 180 (* h2 h2) h3 (* h5 h5) h6 (* 
j2 j2)) (* 84 (* h2 h2) h3 (* h5 h5) h6 j2) (* 16 (* h2 h2) h3 (* h5 h5) h6) (* 
3 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 (* h2 h2) h3 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 118 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 202
 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 183 (* h2 h2) h3 h5 (* h6 h6) (* j2 
j2)) (* 85 (* h2 h2) h3 h5 (* h6 h6) j2) (* 16 (* h2 h2) h3 h5 (* h6 h6)) (* 6 
(* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 28 (* h2 h2) h3 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* 52 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2)) (* 48 (* h2 h2) 
h3 (* h6 h6 h6) (* j2 j2)) (* 22 (* h2 h2) h3 (* h6 h6 h6) j2) (* 4 (* h2 h2) h3
 (* h6 h6 h6)) (* (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2
) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 20 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15 (* h2 h2) (* h5 h5 
h5) h6 (* j2 j2)) (* 6 (* h2 h2) (* h5 h5 h5) h6 j2) (* (* h2 h2) (* h5 h5 h5) 
h6) (* 2 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 30 (* h2 h2) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 40 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 30 (* h2 h2) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 12 (* h2 h2) (* h5 h5) (* h6 h6) j2) (* 2 (* 
h2 h2) (* h5 h5) (* h6 h6)) (* (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 6 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h2 h2) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 20 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 15 (* h2 
h2) h5 (* h6 h6 h6) (* j2 j2)) (* 6 (* h2 h2) h5 (* h6 h6 h6) j2) (* (* h2 h2) 
h5 (* h6 h6 h6)) (* h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 15 h2 
(* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 87 h2 (* h3 h3 h3) (* h5 h5) (* j2
 j2 j2 j2)) (* 245 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 348 h2 (* h3 h3 h3
) (* h5 h5) (* j2 j2)) (* 240 h2 (* h3 h3 h3) (* h5 h5) j2) (* 64 h2 (* h3 h3 h3
) (* h5 h5)) (* 12 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3 
h3) h5 h6 (* j2 j2 j2 j2)) (* 476 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 744 h2 
(* h3 h3 h3) h5 h6 (* j2 j2)) (* 512 h2 (* h3 h3 h3) h5 h6 j2) (* 128 h2 (* h3 
h3 h3) h5 h6) (* 36 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 228 h2 (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2)) (* 400 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 
272 h2 (* h3 h3 h3) (* h6 h6) j2) (* 64 h2 (* h3 h3 h3) (* h6 h6)) (* h2 (* h3 
h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 54 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 116 h2 (* h3 h3)
 (* h5 h5 h5) (* j2 j2 j2)) (* 129 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2)) (* 72 h2
 (* h3 h3) (* h5 h5 h5) j2) (* 16 h2 (* h3 h3) (* h5 h5 h5)) (* 3 h2 (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 42 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 208 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 466 h2 (* h3 h3) 
(* h5 h5) h6 (* j2 j2 j2)) (* 525 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2)) (* 292 h2
 (* h3 h3) (* h5 h5) h6 j2) (* 64 h2 (* h3 h3) (* h5 h5) h6) (* 24 h2 (* h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 184 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2
)) (* 472 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 552 h2 (* h3 h3) h5 (* h6 
h6) (* j2 j2)) (* 304 h2 (* h3 h3) h5 (* h6 h6) j2) (* 64 h2 (* h3 h3) h5 (* h6 
h6)) (* 36 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 120 h2 (* h3 h3) (* h6 
h6 h6) (* j2 j2 j2)) (* 148 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 80 h2 (* h3 
h3) (* h6 h6 h6) j2) (* 16 h2 (* h3 h3) (* h6 h6 h6)) (* 2 h2 h3 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 18 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 60 h2
 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 100 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) 
(* 90 h2 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 42 h2 h3 (* h5 h5 h5) h6 j2) (* 8 h2 
h3 (* h5 h5 h5) h6) (* 3 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 33 
h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 118 h2 h3 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 202 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 183 h2 h3 (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 85 h2 h3 (* h5 h5) (* h6 h6) j2) (* 16 h2 h3 (* 
h5 h5) (* h6 h6)) (* 12 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 56 h2 h3 h5
 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 104 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 96 
h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 44 h2 h3 h5 (* h6 h6 h6) j2) (* 8 h2 h3 h5 
(* h6 h6 h6)) (* h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2
 j2)) (* 20 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 15 h2 (* h5 h5 h5) (* h6 
h6) (* j2 j2)) (* 6 h2 (* h5 h5 h5) (* h6 h6) j2) (* h2 (* h5 h5 h5) (* h6 h6)) 
(* h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h2 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 15 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 20 
h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 15 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2
)) (* 6 h2 (* h5 h5) (* h6 h6 h6) j2) (* h2 (* h5 h5) (* h6 h6 h6)) (* 6 (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2
 j2 j2)) (* 238 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 372 (* h3 h3 h3) (* 
h5 h5) h6 (* j2 j2)) (* 256 (* h3 h3 h3) (* h5 h5) h6 j2) (* 64 (* h3 h3 h3) (* 
h5 h5) h6) (* 36 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 228 (* h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2)) (* 400 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 272 
(* h3 h3 h3) h5 (* h6 h6) j2) (* 64 (* h3 h3 h3) h5 (* h6 h6)) (* 6 (* h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 46 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2)) (* 118 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 138 (* h3 h3) (* h5 h5 h5
) h6 (* j2 j2)) (* 76 (* h3 h3) (* h5 h5 h5) h6 j2) (* 16 (* h3 h3) (* h5 h5 h5)
 h6) (* 12 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 92 (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 236 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2)) (* 276 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2)) (* 152 (* h3 h3) (* h5 h5) 
(* h6 h6) j2) (* 32 (* h3 h3) (* h5 h5) (* h6 h6)) (* 36 (* h3 h3) h5 (* h6 h6 
h6) (* j2 j2 j2 j2)) (* 120 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 148 (* h3
 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 80 (* h3 h3) h5 (* h6 h6 h6) j2) (* 16 (* h3 
h3) h5 (* h6 h6 h6)) (* 6 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 28 h3
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 52 h3 (* h5 h5 h5) (* h6 h6) (* j2 
j2 j2)) (* 48 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 22 h3 (* h5 h5 h5) (* h6 
h6) j2) (* 4 h3 (* h5 h5 h5) (* h6 h6)) (* 6 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 28 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 52 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2)) (* 48 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 22 h3 
(* h5 h5) (* h6 h6 h6) j2) (* 4 h3 (* h5 h5) (* h6 h6 h6))) 0)))
(check-sat)
(exit)
