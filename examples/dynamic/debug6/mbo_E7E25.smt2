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
(set-info :instance |E7E25|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-const j2 Real)
(declare-const h6 Real)
(declare-const h5 Real)
(declare-const h4 Real)
(declare-const h3 Real)
(declare-const h2 Real)
(declare-const h1 Real)
(assert (and (> h1 0) (> h2 0) (> h3 0) (> h4 0) (> h5 0) (> h6 0) (> j2 0) (= 
(+ (* 6 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 42 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 
h1) (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2)
 (* h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3
 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 
(* j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 
j2)) (* 6 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6 
(* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1 
h1) (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1 h1) (* h2 
h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1 h1) (* h2 h2 h2) h3 h5 
h6 (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
(* h1 h1 h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 
h1 h1) (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) (* h2
 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) (* h2 h2 h2) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* 
j2 j2 j2 j2 j2 j2)) (* 354 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2
 j2 j2)) (* 420 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 
144 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 2 (* h1 h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) 
(* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 174 (* h1 h1 h1 h1) (* h2
 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 376 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) (* 328 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
h6 (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)
) (* (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 29 
(* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1
 h1 h1) (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1) (* 
h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3)
 h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6
 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2
 j2 j2 j2)) (* 40 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 
12 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 96
 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 132 (* 
h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 5 (* h1 h1 h1 h1) (* h2 
h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1 h1) (* h2 h2)
 (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 213 (* h1 h1 h1 h1) (* h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 250 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 92 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) h5 h6 (* j2 
j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 40 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 112 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 116 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 40 (* h1 h1 h1 h1) (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* (* h1 h1
 h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 17 (* h1 h1 h1 h1
) (* h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h2 
h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2))
 (* 2 (* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 
(* h1 h1 h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 
h1 h1) (* h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) (* h2 
h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) (* h2 h2) h3
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5 
h5) (* j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 42 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1 h1 h1) (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 6 
(* h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* 
h1 h1 h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 
h1 h1) (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) 
(* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) (* h2 h2) h3 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6) (* j2 
j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* (* h1 h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 
h1 h1 h1) (* h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) 
(* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* 
h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) (* h2 h2) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30
 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 235 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 630 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 616 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4
 h5 (* j2 j2 j2 j2)) (* 192 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) 
(* 4 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 
(* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 188 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 320 (* h1 h1 h1 h1) h2 
(* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4
 h6 (* j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) 
(* 36 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 312
 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 588 (* h1 
h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 408 (* h1 h1 h1 h1) 
h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) h2 (* h3 h3 h3)
 (* h5 h5) (* j2 j2 j2)) (* 24 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 258 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 832 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
1142 (* h1 h1 h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 704 (* h1 h1 
h1 h1) h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 160 (* h1 h1 h1 h1) h2 (* h3 h3
 h3) h5 h6 (* j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 508 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 560 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 304 (* h1 h1 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 64 (* h1 h1
 h1 h1) h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 3 (* h1 h1 h1 h1) h2 (* h3 h3
) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 37 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 98 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5
 (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2
 j2)) (* 4 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 20 (* h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 32 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1)
 h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 (* h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 182 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 228 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)
) (* 8 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 114
 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 340 (* h1 h1
 h1 h1) h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 362 (* h1 h1 h1 h1) h2 
(* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1 h1) h2 (* h3 h3) h4 h5
 h6 (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 104 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 96 (* h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 (* 
h1 h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) h2
 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) h2 (* h3
 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 36 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 218 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 380 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* 262 (* h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 (* 
h1 h1 h1 h1) h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 280 (* h1 h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1 h1 h1) h2 (* h3
 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 260 (* h1 h1 h1 h1) h2 (* h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1) h2 (* h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 76 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 100 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 64 (* h1 h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h1 
h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) h2 h3 (* h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1 h1) h2 h3 (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 11 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 6 (* h1 h1 h1 h1) h2 h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1 
h1) h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) h2 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1 h1 h1) h2 h3 h4 (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5 h5) (* 
j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 48 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 70 (* h1 h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h1 
h1 h1 h1) h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1 h1) h2 h3 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) h2 h3 h4 h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 35 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 12 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 32 (* h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28 (* 
h1 h1 h1 h1) h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) 
h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 35 (* h1 h1 h1 h1) h2 h3 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 69 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 53 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1 h1) h2 h3 (* h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 20 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 34 (* h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* 
h1 h1 h1 h1) h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) 
h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* (* h1 h1 h1 h1) h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1
 h1 h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 
h1) h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) h2 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1 h1) h2 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* (* h1 h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
28 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 134 
(* h1 h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 268 (* h1 h1
 h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 224 (* h1 h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1) (* h3 h3 h3) (* h4
 h4) h5 (* j2 j2 j2)) (* 6 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 306 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 460 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 288
 (* h1 h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1
) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 290 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 806 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 1020 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 
592 (* h1 h1 h1 h1) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 128 (* h1 h1 h1 h1
) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 36 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 796 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 368 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 64 (* h1 h1 h1 h1) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 12 (* h1 h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1 h1
 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 532 (* h1 h1 h1 
h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 932 (* h1 h1 h1 h1) 
(* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1 h1) (* h3 h3
 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 368 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2 j2)) (* 64 (* h1 h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2
 j2)) (* 2 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 14 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 28 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1)
 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1 h1) (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1 h1 h1) (* h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 44 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 128 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 136 (* h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 48 (* 
h1 h1 h1 h1) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) (* 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1 h1) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1 h1 h1) (* h3 h3) h4
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2)) (* 3 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 43 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 217 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 373 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
260 (* h1 h1 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1
 h1 h1) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1 h1) (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1 h1) (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h1 h1 h1 h1) (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 270 (* h1 h1 h1 h1) (* h3 h3) h4 h5
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 188 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1 h1) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2
 j2 j2)) (* 36 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 120 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 148 (* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 80 
(* h1 h1 h1 h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1 
h1) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 18 (* h1 h1 h1 h1) (* h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 126 (* h1 h1 h1 h1) (* h3
 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 298 (* h1 h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 322 (* h1 h1 h1 h1) (* 
h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1 h1) (* h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1 h1) (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 148 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 16 (* h1 h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* (* h1 
h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1 
h1) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h3 (* 
h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 2 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 18 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 28
 (* h1 h1 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1
 h1 h1) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1 h1) h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1 h1) h3 h4 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1 h1 h1) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 27 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1 h1) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 19 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
47 (* h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 41 (* 
h1 h1 h1 h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1 
h1) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1 h1) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) h3 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1 h1) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 18 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 4 (* h1 h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h1 
h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) (* h2
 h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3
 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 
(* j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2 
j2)) (* 6 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 3 (* 
h1 h1 h1) (* h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) (* 
h2 h2 h2 h2) h3 h5 h6 (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2 h2) h3 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2 h2 h2) (* h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* (* h1 h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
24 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2)) (* 210 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 444 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3 h3) h5 (* j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 86 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 
j2 j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 j2)) 
(* 392 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 192 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 176 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 
h5 (* j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 (* j2 j2
 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 60 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 128 
(* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1)
 (* h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 42 (* h1 h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h5 h5) (* j2 j2 j2 j2)) (* 19 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 122 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 282 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2 j2
)) (* 184 (* h1 h1 h1) (* h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 12 (* h1
 h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 74 (* h1 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1 
h1) (* h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2 h2) h3 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 42 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 32 (* h1 h1 h1) (* h2 h2 h2) h3 h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1
) (* h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* 
h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2 h2) 
h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 47 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 32 (* h1 h1 h1) (* h2 h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 (* h1 
h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1)
 (* h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) (* h2 h2
 h2) h3 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 
h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* 
h2 h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 
h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2 h2) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2 h2) h5 (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 
j2 j2 j2)) (* 180 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2 j2
)) (* 864 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 1392 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 576 (* h1 h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 
h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 408 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 1040 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* 
j2 j2 j2 j2 j2)) (* 1120 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2 
j2)) (* 384 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1)
 (* h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 520 (* h1 h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 1588 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 1608 (* h1 h1 h1) (* h2 h2) (* h3 h3 
h3) h4 h5 (* j2 j2 j2 j2)) (* 576 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 (* 
j2 j2 j2)) (* 10 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 138 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 592 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 
1032 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 736 (* h1 
h1 h1) (* h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 
h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 42 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 396 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1014 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 936 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) 
(* j2 j2 j2 j2)) (* 288 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2)) (* 17 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 226 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
1075 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2224 
(* h1 h1 h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 1752 (* h1 h1 
h1) (* h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 480 (* h1 h1 h1) (* h2 h2) 
(* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 14 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 720 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1192 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 
h6) (* j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* 
j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2))
 (* 7 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 105 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
314 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 192 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 14 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 79 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 432 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 580 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 240 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2)) (* 23 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 234 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 748 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2
 j2)) (* 940 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 
384 (* h1 h1 h1) (* h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 12 (* h1 h1 h1
) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 102 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 276 (* h1 h1 
h1) (* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 288 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h2 h2
) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 36 (* h1 h1 h1) (* h2 h2) (* h3 h3)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 150 (* h1 h1 h1) (* h2 h2) (* h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 186 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 72 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 21 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 607 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2 j2)) (* 604 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 192 (* h1 h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 35 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 273 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 688 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
626 (* h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 192 (* 
h1 h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1)
 (* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 200 (* h1 h1 h1) 
(* h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1 h1) (* 
h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) (* h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 43 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4 (* h1 h1 h1) (* h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 
h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1 
h1) (* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 55 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1 h1) (* h2 h2)
 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 97 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) (* h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 15 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 80 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 106 (* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 
(* h1 h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) 
(* h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* 
h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h2 h2) 
h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) h3 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 49 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 24 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
23 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 103 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 120 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
42 (* h1 h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 (* h1
 h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 (* h1 h1
 h1) (* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 63 (* h1 h1 h1) 
(* h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) (* h2 h2)
 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) h3 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 3 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 6 (* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 
(* h1 h1 h1) (* h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 
h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1
 h1) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1
) (* h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 
h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h2 h2) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2) (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) (* h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* (* h1 h1 h1) (* h2 h2) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 62 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1 
h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 1672 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 2080 (* h1 h1 h1) h2 (* h3 h3 h3 h3) 
h4 h5 (* j2 j2 j2 j2)) (* 768 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)
) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 104
 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1
 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) h2 (* 
h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4
 h6 (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2)) 
(* 72 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 696
 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1728 (* h1 
h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1440 (* h1 h1 h1) h2 
(* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 384 (* h1 h1 h1) h2 (* h3 h3 h3 h3
) (* h5 h5) (* j2 j2 j2)) (* 48 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 564 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 2132 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 3480 (* h1 h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 2496 (* h1 
h1 h1) h2 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 640 (* h1 h1 h1) h2 (* h3 h3
 h3 h3) h5 h6 (* j2 j2 j2)) (* 8 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 568 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 1392 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1760 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 1088 (* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 256 
(* h1 h1 h1) h2 (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 7 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 143 (* h1 h1 h1) h2 (* h3
 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 776 (* h1 h1 h1) h2 (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 1548 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1104 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) 
(* 12 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
100 (* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 288 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 336 (* h1 h1
 h1) h2 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h2 (* 
h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 19 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 386 (* h1 h1 h1) h2 (* h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1717 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2444 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 
j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 4 (* 
h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 155 (* h1 
h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1145 (* h1 h1 h1
) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3296 (* h1 h1 h1) h2 (* 
h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4352 (* h1 h1 h1) h2 (* h3 h3 h3) 
h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 2512 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2 j2)) (* 512 (* h1 h1 h1) h2 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 12 (* 
h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 488 
(* h1 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 912 (* h1
 h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 800 (* h1 h1 h1) 
h2 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 h3
 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 144 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 576 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2
 j2 j2 j2)) (* 192 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 132 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 900 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2404 (* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2736 
(* h1 h1 h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1392 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) h2 (* h3 
h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 28 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 306 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1350 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2816 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2884 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 1408 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2))
 (* 256 (* h1 h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 12 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 112 (* h1 h1
 h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 388 (* h1 h1 
h1) h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1 h1) 
h2 (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1 h1) h2 (* h3
 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h2 (* h3 h3 h3) (* 
h6 h6 h6) (* j2 j2 j2 j2)) (* 9 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2)) (* 160 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 64 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 4 (* h1 h1 
h1) h2 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2
 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 (* h3 h3
) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 141 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 500 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 464 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2)) (* 28 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 241 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 618 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 620 (* h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 192 (* 
h1 h1 h1) h2 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 (* 
h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1 h1) h2 
(* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 (* h3
 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 221 (* h1 h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 431 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 292 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 
j2)) (* 6 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 178 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 817 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 1457 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1044
 (* h1 h1 h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1 
h1) h2 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h2 (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 198 (* h1 h1 h1) h2 (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 676 (* h1 h1 h1) h2 (* h3 h3
) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1070 (* h1 h1 h1) h2 (* h3 h3) h4
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 760 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 32 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 92 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 112 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
48 (* h1 h1 h1) h2 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1 
h1) h2 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1) h2
 (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h2 (* h3 h3
) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 346 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 502 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 64 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 
28 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 241 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 740 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 971 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 580 (* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 128 
(* h1 h1 h1) h2 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1 h1
) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h1 h1 
h1) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 444 (* h1 h1 h1
) h2 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 530 (* h1 h1 h1) h2 
(* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 300 (* h1 h1 h1) h2 (* h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) h2 (* h3 h3) h5 (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5 
(* h1 h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 30 (* h1 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2
 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5 (* h1 h1 h1) h2 h3 (* h4 h4 
h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h2 h3 (* h4 h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 16 
(* h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 (* 
h1 h1 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 125 (* h1 h1
 h1) h2 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 
h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9 (* h1 h1 h1) h2 h3 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) h2 h3 (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h2 h3 (* h4 h4) h5 (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 11 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 10 (* h1 h1 h1) h2 h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* 
h1 h1 h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 129 (* h1 h1 
h1) h2 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 115 (* h1 h1 h1) h2 h3
 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) h2 h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2)) (* 13 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 77 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 182 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2)) (* 48 (* h1 h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 4 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 25
 (* h1 h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 41 (* h1 
h1 h1) h2 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h2 
h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) h2 h3 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h2 h3 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 57 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 98 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 67 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
16 (* h1 h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 13 (* h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 61 (* h1 h1 
h1) h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 97 (* h1 h1 h1)
 h2 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 65 (* h1 h1 h1) h2 h3
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 h3 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h2 h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* (* h1 h1 h1) h2 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* 
h1 h1 h1) h2 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 
h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 
h1) h2 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) 
h2 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h2 h4 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1 h1) h2 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 2 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 4 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 2 (* h1 h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2 (* h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* 
h1 h1 h1) h2 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 
h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1 h1)
 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 320 (* h1 h1 h1) (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 752 (* h1 h1 h1) (* h3 h3 h3
 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 768 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 
h4) h5 (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 
j2 j2)) (* 12 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 164 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 752 (* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1392 
(* h1 h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 1024 (* h1 h1 
h1) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 4 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 660 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 2112 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2
)) (* 3152 (* h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 2112 (* 
h1 h1 h1) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 512 (* h1 h1 h1) (* h3 h3
 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 72 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 744 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2192 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 2592 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 1344 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 256 (* h1 h1 h1) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 24 (* h1 h1 h1
) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h1 h1 
h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1320 (* h1 h1 
h1) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2672 (* h1 h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2720 (* h1 h1 h1) (* h3 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1344 (* h1 h1 h1) (* h3 h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2)) (* 6 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 62 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 
j2)) (* 220 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
304 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 128 (* h1 
h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* (* h1 h1 h1) (* h3 h3 h3
) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 307 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 844 (* h1 h1 h1) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1 h1) (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 110 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 596 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1304 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2 j2 j2)) (* 1200 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2)) (* 384 (* h1 h1 h1) (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) 
(* 24 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
184 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 448 
(* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1
 h1) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 17 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 (* h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1621 (* h1 h1 h1) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2816 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2016 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2)) (* 512 (* h1 h1 h1) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2
 j2)) (* 42 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 392 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 1346 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2108 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
1488 (* h1 h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 384 (* h1 
h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 144 (* h1 h1 h1) (* h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1 h1) (* h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 928 (* h1 h1 h1) (* h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 576 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5
 h5) h6 (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2)) (* 66 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2 j2)) (* 488 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1514 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 2012 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 1184 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 36 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 288 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 812 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1024 (* h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 592 (* 
h1 h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 (* h1 h1 h1) 
(* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 50 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 120 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 4 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 42 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
100 (* h1 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1
 h1 h1) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 125 (* h1 h1 h1
) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 164 (* h1 h1 h1)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 106 (* h1 h1 h1) (* h3
 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 398 (* h1 h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 496 (* h1 h1 h1) (* 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1 h1) (* h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) (* h3 h3) (* h4
 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h3 h3) 
(* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 170 (* h1 h1 h1) (* h3 h3
) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 228 (* h1 h1 h1) (* h3 h3)
 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1) (* h3 h3) (* 
h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2)) (* 13 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 194 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 469 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 416 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
128 (* h1 h1 h1) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 56 (* h1 h1
 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 324 (* 
h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 716 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 632 
(* h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 (* 
h1 h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1
) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1 h1
) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 222 (* h1 h1 h1) 
(* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 204 (* h1 h1 h1) (* h3
 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) h4 
h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2)) (* 42 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 208 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 354 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 252 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 48 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 224 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 368 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 256 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 64 (* h1 h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 12 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 56 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
92 (* h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* 
h1 h1 h1) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1)
 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h3 (* h4 h4 h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h3 (* h4 h4 h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 17 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 16 (* h1 h1 h1) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
(* h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 5 (* 
h1 h1 h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 
h1) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26 (* h1 h1 h1) h3 (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1 h1) h3 (* h4 
h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h3 (* h4 h4) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 45 (* h1 h1 h1) h3 (* h4 h4) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1 h1) h3 (* h4 h4) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 19 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2
)) (* 14 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 56 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 66 (* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 
(* h1 h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1 
h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 34 (* h1 h1 
h1) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43 (* h1 h1 h1)
 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h3 h4
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1 h1) h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1 h1) h3 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 14 (* h1 h1 h1) h3 (* h5 h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1 h1) h3 (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2 j2 j2)) (* 8 (* h1 h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 6 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 16 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 14 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4 (* h1 h1 h1) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2
 h2 h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 144 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3 h3) h5 (* j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 
j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2 
j2)) (* 112 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 96 (* 
h1 h1) (* h2 h2 h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2 h2
) (* h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 28 (* h1 h1) (* h2 h2 h2 h2) (* h3 
h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h5 
(* j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 
j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 
40 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 24 (* h1 h1) 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2
 h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 11 (* h1 h1) (* h2 h2 h2 h2) (* 
h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5
 h6 (* j2 j2 j2 j2 j2)) (* 92 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) h5 h6 (* j2 j2
 j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* 32 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 40
 (* h1 h1) (* h2 h2 h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* (* h1 h1) (* 
h2 h2 h2 h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 
h2) h3 h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 
h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 h4 h5 h6 (* j2 j2 
j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h1 
h1) (* h2 h2 h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2 
h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2 h2 h2) h3 h5 (* h6 h6) (* j2 j2
 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* 4 (* h1 h1) (* h2 h2 h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* h1 
h1) (* h2 h2 h2 h2) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2
 h2 h2) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2 h2) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2 h2 h2) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2 h2) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2
 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2 j2)) 
(* 672 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 576 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) (* h3 
h3 h3 h3) h6 (* j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3
) h6 (* j2 j2 j2 j2 j2)) (* 640 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 
j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3 h3) h6 (* j2 j2 j2)) (* 4 
(* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 125 (* h1
 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 682 (* h1 h1) (* 
h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 1176 (* h1 h1) (* h2 h2 h2) 
(* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 576 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
h4 h5 (* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 196 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2
 j2)) (* 544 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 
592 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 192 (* h1 h1) 
(* h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2) (* h3
 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 378 (* h1 h1) (* h2 h2 h2) (* h3 h3 
h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 600 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* 
h5 h5) (* j2 j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* 
j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 265 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 
894 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 1216 (* h1 
h1) (* h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 480 (* h1 h1) (* h2 h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 196 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* 
h6 h6) (* j2 j2 j2 j2 j2)) (* 592 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) 
(* j2 j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 
j2)) (* 4 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)
) (* 71 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 
250 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 192 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 10 (* h1 h1) (* 
h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 60 (* h1 h1) (* h2
 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 104 (* h1 h1) (* h2 h2 
h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 146 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 400 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2)) (* 240 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2)) (* 52 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 312 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2
)) (* 670 (* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 384 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2
 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1) (* h2 
h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 224 (* h1 h1) (* h2 h2 
h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 108 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 72 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) 
(* j2 j2 j2 j2)) (* 33 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 197 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 390 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 192 (* h1 h1) (* h2 h2 h2) (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 48
 (* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 243 
(* h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 424 (* 
h1 h1) (* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 192 (* h1 h1) 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 14 (* h1 h1) (* h2 h2 h2
) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 76 (* h1 h1) (* h2 h2 h2) 
(* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1) (* h2 h2 h2) (* 
h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2 h2) (* h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 42 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2)) (* 13 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 37 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 18 (* h1 h1) (* h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 2 (* h1 
h1) (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1)
 (* h2 h2 h2) h3 (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2
 h2 h2) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 35 (* h1 h1) (* h2 h2 h2
) h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 30 (* h1 h1) (* h2 h2 h2) h3 h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 30 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 110 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 84 (* h1 h1) (* h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 30 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 81 (* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 
(* h1 h1) (* h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* 
h2 h2 h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2 
h2) h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h2 h2 h2) h3 (* 
h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 11 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 27 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 75 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 42 (* h1 h1) (* h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
17 (* h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* 
h1 h1) (* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) 
(* h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2 h2) 
h3 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2) h3 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2 h2) (* h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 7 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 6 (* h1 h1) (* h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1) (* h2 h2 h2) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* 
h1 h1) (* h2 h2 h2) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) 
(* h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* 
h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* h2 h2 
h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h2 h2 h2)
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2 h2) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h4 h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 
h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 872 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 
(* j2 j2 j2 j2 j2 j2)) (* 2904 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 
j2 j2 j2 j2)) (* 3776 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2))
 (* 1536 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 16 (* h1 h1)
 (* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 216 (* h1 h1) 
(* h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 976 (* h1 h1) (* h2
 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 1952 (* h1 h1) (* h2 h2) 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 1728 (* h1 h1) (* h2 h2) (* h3 h3 
h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 512 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h4 h6 
(* j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 300 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1272 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 1920 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 768 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 10 (* h1 h1) (* 
h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 (* h1 h1) (* h2
 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1168 (* h1 h1) (* h2 h2)
 (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3224 (* h1 h1) (* h2 h2) (* h3 
h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 3680 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) 
h5 h6 (* j2 j2 j2 j2)) (* 1280 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 
j2 j2)) (* 16 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 216 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 976 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1952 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 1728 (* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 512 
(* h1 h1) (* h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 5 (* h1 h1) (* h2
 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 139 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 908 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2036 (* h1 h1) (* h2 
h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 1616 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 496 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 624 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 
(* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 
j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 232 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 1372 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 2744 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)
) (* 1888 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 384 
(* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 62 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 694 (* h1 h1) (* h2
 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2854 (* h1 h1) (* h2 h2)
 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4988 (* h1 h1) (* h2 h2) (* h3 
h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 3408 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 
h5 h6 (* j2 j2 j2 j2)) (* 768 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2
 j2)) (* 40 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 360 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 1088 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1312 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 512 (* h1 h1) (* h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 42 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 300 (* 
h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 672 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* 
h2 h2) (* h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 25 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 338 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1501 (* h1 h1) (* h2 h2) 
(* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2652 (* h1 h1) (* h2 h2) (* 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1744 (* h1 h1) (* h2 h2) (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h5 
h5) h6 (* j2 j2 j2)) (* 61 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 571 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 1962 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2952 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2)) (* 1792 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2)) (* 384 (* h1 h1) (* h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 24 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
204 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
592 (* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 688 
(* h1 h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h1 
h1) (* h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h1 h1) (* h2 
h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 248 (* h1 h1) (* h2 h2) 
(* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3
) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4
) h6 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 614 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 664 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 192 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5)
 (* j2 j2 j2 j2)) (* 34 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 262 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 724 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 
j2 j2 j2 j2 j2)) (* 868 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2))
 (* 8 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 56 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 128 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 6 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 134 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 453 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2))
 (* 412 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 96 
(* h1 h1) (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 68 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 551 (* h1 h1
) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1485 (* h1 h1
) (* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1356 (* h1 h1) 
(* h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1) (* h2 
h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 82 (* h1 h1) (* h2 h2) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 526 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1120 (* h1 h1) (* h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 992 (* h1 h1) (* h2 h2) (* h3 
h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 288 (* h1 h1) (* h2 h2) (* h3 h3) h4 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* h2 h2) (* h3 h3) h4 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 54 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2)) (* 17 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 167 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 437 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 376 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 96 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 64 (* h1
 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 403
 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
870 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
692 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 192
 (* h1 h1) (* h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 48 (* h1 
h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 276 (* 
h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 512 (* 
h1 h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 372 (* h1 
h1) (* h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 96 (* h1 h1) (* 
h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 (* h1 h1) (* h2 h2) (* h3
 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h1 h1) (* h2 h2) (* 
h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h2 h2) (* h3
 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h2 h2) (* h3 h3) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 7 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 46 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 10 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 12 (* h1 h1) (* h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2)) (* 3 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 40 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 70 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 24 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 20 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 94
 (* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 169 
(* h1 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 72 (* h1
 h1) (* h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* 
h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 43 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) 
(* h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) (* h2 h2
) h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 (* h1 h1) (* h2 h2) 
h3 h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 h2) h3 h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 121 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 151 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 47 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 172 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 200 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 72 (* h1 h1) (* h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 18 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
56 (* h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* 
h1 h1) (* h2 h2) h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* 
h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 (* h1 h1) (* h2 
h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) (* h2 h2) h3
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 22 (* h1 h1) (* h2 h2) h3 (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 81 (* h1 h1) (* h2 h2) h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 81 (* h1 h1) (* h2 h2) h3 (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 27 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 85 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 77 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2)) (* 9 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 23 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 12 (* h1 h1) (* h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1) (* h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
3 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
4 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 
(* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 6 (* h1 h1) (* h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
2 (* h1 h1) (* h2 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1
 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1
 h1) (* h2 h2) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1
) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1
) (* h2 h2) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) 
(* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) 
(* h2 h2) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* 
h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) (* 
h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 
h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) (* h2 
h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h2 (* h3
 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 232 (* h1 h1) h2 (* h3 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 h1) h2 (* h3 h3 
h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 2912 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2752 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) 
h5 (* j2 j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2
)) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 128 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
384 (* h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 512 (* 
h1 h1) h2 (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 28 (* h1 h1) h2 (* h3 h3 h3 h3)
 h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 530 (* h1 h1) h2 (* h3 h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2484 (* h1 h1) h2 (* h3 h3 h3 h3) h4 
(* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4480 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 3200 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 8 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 232 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1644 (* h1 h1
) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 5200 (* h1 h1) h2 (* 
h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 8240 (* h1 h1) h2 (* h3 h3 h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 6144 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* 
j2 j2 j2 j2)) (* 1536 (* h1 h1) h2 (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 16 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160
 (* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 640 
(* h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1280 (* 
h1 h1) h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1280 (* h1 h1) 
h2 (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1) h2 (* h3 h3
 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 72 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2 j2 j2)) (* 864 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 
j2 j2 j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 72 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
748 (* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2856 
(* h1 h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 4768 (* h1 
h1) h2 (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3328 (* h1 h1) h2 (* 
h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3 h3) 
(* h5 h5) h6 (* j2 j2 j2)) (* 16 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 260 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 1460 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 3888 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 5264 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 3392 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 
768 (* h1 h1) h2 (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) h2
 (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) h2 
(* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h1 h1) h2 (* h3
 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3 
h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) h2 (* h3 h3 h3 h3) (* h6 
h6 h6) (* j2 j2 j2 j2)) (* 14 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 180 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 
j2 j2 j2 j2 j2)) (* 688 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2
 j2 j2)) (* 960 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) 
(* 384 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 (* h1 h1)
 h2 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2
 (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h1 h1) h2 (* h3
 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) h2 (* h3 h3 h3) 
(* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 79 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 799 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2352 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4
) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2384 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2)) (* 12 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 234 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1298 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 3132 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 3328 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2))
 (* 1152 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 8 (* h1 
h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 72 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
240 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
352 (* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 
(* h1 h1) h2 (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 55 (* h1 h1
) h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 574 (* h1 h1) 
h2 (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1480 (* h1 h1) h2 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1312 (* h1 h1) h2 (* h3 
h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2)) (* 22 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 459 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2494 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 5580 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 5056 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2)) (* 1536 (* h1 h1) h2 (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) 
(* 56 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 574 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 2264 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
4280 (* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3776 
(* h1 h1) h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1152 (* h1 h1) 
h2 (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 16 (* h1 h1) h2 (* h3 h3 h3)
 h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 (* h1 h1) h2 (* h3 h3 h3
) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 336 (* h1 h1) h2 (* h3 h3 h3) 
h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1) h2 (* h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3 h3) h4 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 168 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2
 j2 j2 j2)) (* 96 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) 
(* 96 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
690 (* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1584 
(* h1 h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1376 (* h1 
h1) h2 (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 384 (* h1 h1) h2 (* 
h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 33 (* h1 h1) h2 (* h3 h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 414 (* h1 h1) h2 (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1703 (* h1 h1) h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3204 (* h1 h1) h2 (* h3 h3 
h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2672 (* h1 h1) h2 (* h3 h3 h3)
 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 768 (* h1 h1) h2 (* h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 44 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 354 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1146 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1836 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 1408 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
8 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
56 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144
 (* h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* 
h1 h1) h2 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) h2
 (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h2 (* h3 h3) 
(* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 (* h1 h1) h2 (* h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4 h4)
 h5 (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 156 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2)) (* 20 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 116 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 248 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2))
 (* 192 (* h1 h1) h2 (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* (* h1 
h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
343 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
476 (* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 192 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 15 (* h1 h1
) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 224 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 842 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1288 
(* h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 576 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) 
h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 118 (* h1
 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 364 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 528 (* 
h1 h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 288 (* h1 
h1) h2 (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14 (* h1 h1) h2 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 117 (* h1 h1) h2 
(* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1) h2 (* h3
 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3) h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 14 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 236 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 864 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1024 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 384 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 54 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 451 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 1230 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2)) (* 1472 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 576 (* h1 h1) h2 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 32 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 176 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 404 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 456 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
192 (* h1 h1) h2 (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h1 h1
) h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 124 (* h1 h1) 
h2 (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) h2 
(* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 19 (* h1 h1) h2 (* h3 h3) (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 190 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 515 (* h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 548 (* h1 h1) h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 39 (* h1 h1) h2 (* h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 243 (* h1 h1) h2 (* h3 h3) (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 544 (* h1 h1) h2 (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 552 (* h1 h1) h2 (* h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) h2 (* h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 78 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 150 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 140 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 3 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 12 (* h1 h1) h2 h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 5 (* 
h1 h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 
h1) h2 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) h2
 h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h2 h3 (* h4
 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 38 (* h1 h1) h2 h3 (* h4 h4
 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 h3 (* h4 h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 51 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 124 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 72 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 8 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 43 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 96 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 72 (* h1 h1) h2 h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 26
 (* h1 h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 
h1) h2 h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) h2 h3 
h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h2 h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 (* h1 h1) h2 h3 h4 (* h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 (* h1 h1) h2 h3 h4 (* h5 h5 h5
) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h1 h1) h2 h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h1 h1) h2 h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 3 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 22 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 31 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 12 (* h1 h1) h2 h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
12 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
46 (* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 60 
(* h1 h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 
h1) h2 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23 (* h1 h1) h2 h3 
(* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 (* h1 h1) h2 h3 (* 
h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h2 h3 (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h4 h4 h4) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h4 h4) (* h5 h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 (* h4 h4) (* h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) h2 h4 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 (* h1 h1) h2 h4 (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* (* h1 h1) h2 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 80 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 288 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 448 
(* h1 h1) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2 (* h1 h1) (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 58 (* h1 h1) (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 420 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1200 (* h1 h1) (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1408 (* h1 h1) (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 768 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 1792 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2)) (* 1920 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2)) (* 768 (* h1 h1) (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 
12 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128
 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 464 (* 
h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 640 (* h1 h1) 
(* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3
 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 18 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 394 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5
 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1988 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3984 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 3392 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* 
j2 j2 j2 j2 j2)) (* 1024 (* h1 h1) (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 56 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 504 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 1776 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3040 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2496
 (* h1 h1) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 768 (* h1 h1) 
(* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 72 (* h1 h1) (* h3 h3 h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1184 (* h1 h1) (* h3 h3 h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 960 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 
j2 j2 j2)) (* 36 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 396 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 1568 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 2704 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 1984 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) 
(* 48 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 368 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 1088 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
1536 (* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1024 
(* h1 h1) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h1 h1) 
(* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3) (* h4 
h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2)) (* 3 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 57 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 296 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 528 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 
j2 j2 j2 j2)) (* 4 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 68 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 288 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2
 j2)) (* 464 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 256 (* h1 h1) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 4 (* h1 
h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 68 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
328 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
544 (* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 256 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1
) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 472 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1588 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1936 
(* h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 768 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 32 (* h1 h1) 
(* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 260 (* h1
 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 752 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 912 (* 
h1 h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 (* h1 
h1) (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 6 (* h1 h1) (* h3
 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 52 (* h1 h1) (* h3 h3
 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h1 h1) (* h3 h3 h3) 
h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) h4 (* h5 
h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 416 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1264 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1376 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 512 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2
 j2 j2)) (* 123 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 913 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 2328 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 2288 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 768 (* h1 h1) (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 52 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 332 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 768 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 752 (* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 
(* h1 h1) (* h3 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 36 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h1 h1) 
(* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 208 (* h1 h1) (* h3
 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 48 (* h1 h1) (* h3 h3 h3) (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 368 (* h1 h1) (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 896 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 832 (* h1 h1) (* h3 h3 h3) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 90 (* h1 h1) (* h3 h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 498 (* h1 h1) (* h3 h3 h3) (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1036 (* h1 h1) (* h3 h3 h3) (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 880 (* h1 h1) (* h3 h3 h3) (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 (* h1 h1) (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 24 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 136 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 272 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 224 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2)) (* 4 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2
 j2)) (* 24 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 32 (* h1 h1) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 2 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 28 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 96 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 64 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 5 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2
)) (* 63 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 164 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 128 (* h1 h1) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2))
 (* (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 15 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 52 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 32 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
22 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 210 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 376 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 192 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 40 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 200 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 348 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 192 (* h1 h1) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 8 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 88 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 140 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 64 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 68 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 346 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 464 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 192 (* h1 h1) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 65 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
 j2 j2)) (* 227 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 300 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 128 (* h1 h1) (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 12 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 68 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 88 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 48 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2 j2)) (* 164 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 184 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 64 (* h1 h1) (* h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 30 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 86 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 92 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 32 (* h1 h1) (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 4 (* h1 h1) h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
(* h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* 
h1 h1) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h3
 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h3
 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h3 
(* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* (* h1 h1) h3 (* h4 h4)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h3 (* h4 h4)
 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h3 (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h1 h1) h3 (* h4 h4) (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 33 (* h1 h1) h3 (* h4 h4) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h1 h1) h3 (* h4 h4)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 7 (* h1 h1) h3 h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 21 (* h1 h1) h3 h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h1 h1) h3 h4 (* h5 h5 h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 13 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 31 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h1 h1) h3 h4 (* h5 h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h3 (* h5 h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 6 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 10 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 4 (* h1 h1) h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) 
(* 48 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 184 h1 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2 h2) (* h3 h3
 h3) h4 h5 (* j2 j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 
j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 96
 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2)
 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 12 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5
) (* j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2)) (* 96 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 6 h1 
(* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 56 h1 (* h2 h2 h2 
h2) (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) (* 168 h1 (* h2 h2 h2 h2) (* h3 h3 h3
) h5 h6 (* j2 j2 j2 j2)) (* 160 h1 (* h2 h2 h2 h2) (* h3 h3 h3) h5 h6 (* j2 j2 
j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48
 h1 (* h2 h2 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2
 h2 h2) (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 
h3 h3) (* h6 h6) (* j2 j2 j2)) (* 3 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 34 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 4
 h1 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2
 h2 h2 h2) (* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2)) (* 80 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 
j2)) (* 18 h1 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 92 h1
 (* h2 h2 h2 h2) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2 h2
) (* h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 32 h1 (* h2 h2 h2 h2) (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)
) (* 6 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 24 h1 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2 h2) 
(* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2 h2) (* h3 h3)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 15 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 58 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 64 h1 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4 h1 (* h2 
h2 h2 h2) (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2)
 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2 h2) (* h3 h3) 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* 
j2 j2 j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 5 h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 6 
h1 (* h2 h2 h2 h2) h3 (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) 
h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2 h2) h3 h4 (* h5 
h5 h5) (* j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2)) (* 28 h1 (* h2 h2 h2 h2) h3 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 10 h1 (* h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* 
h2 h2 h2 h2) h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2 h2) h3 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 8 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 14 h1 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)
) (* 5 h1 (* h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 6 h1 (* 
h2 h2 h2 h2) h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) h4 (* h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2 h2) h4 (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* h1 (* h2 h2 h2 h2) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)
) (* h1 (* h2 h2 h2 h2) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 104 h1 (* h2 h2 
h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2 j2 j2 j2)) (* 560 h1 (* h2 h2 h2) (* h3 h3
 h3 h3) h4 h5 (* j2 j2 j2 j2 j2)) (* 1120 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 
(* j2 j2 j2 j2)) (* 768 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 
16 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* 
h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) 
(* h3 h3 h3 h3) h4 h6 (* j2 j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3)
 h4 h6 (* j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h6 (* j2 j2 j2
)) (* 24 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 192
 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 480 h1 (* h2 
h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h5 h5) (* j2 j2 j2)) (* 12 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 
(* j2 j2 j2 j2 j2 j2 j2)) (* 136 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 560 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 992 h1 (* h2 h2 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 640 h1 (* h2 h2
 h2) (* h3 h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3 h3) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6
 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2
)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h2
 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 174 h1 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 644 h1 (* h2 h2 h2) (* 
h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 816 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 (* j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* j2 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 96 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 192 h1 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 128 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 197 h1 (* h2 h2 h2) (* h3
 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 732 h1 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 896 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5
) (* j2 j2 j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)
) (* 60 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 496 
h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1448 h1 (* h2 h2
 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 1648 h1 (* h2 h2 h2) (* h3 h3 
h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 512 h1 (* h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2)) (* 32 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 192 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 
384 h1 (* h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 256 h1 (* 
h2 h2 h2) (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h3
 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h2 h2 h2) (* h3 h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2)) (* 24 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 
j2 j2 j2 j2)) (* 219 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 672 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
784 h1 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 256 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 48 h1 (* h2 h2 h2) (* h3 h3 h3
) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 322 h1 (* h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 804 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 832 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 
j2 j2)) (* 256 h1 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) (* 16 h1 
(* h2 h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 (* h2 
h2 h2) (* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) 
(* h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3 h3
) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 5 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 54 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2
 j2)) (* 64 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 4 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 
h2 h2) (* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) 
(* h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 15 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 156 h1 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 320 h1 (* h2 h2 h2) (* h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2)) (* 41 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2
 j2 j2 j2 j2 j2 j2)) (* 232 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 
j2 j2 j2 j2)) (* 420 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2
)) (* 192 h1 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 12 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 
(* h2 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2
 h2 h2) (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 7 h1 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 89 h1 (* h2 h2 h2) (* h3 
h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 188 h1 (* h2 h2 h2) (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5)
 (* j2 j2 j2 j2)) (* 58 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 357 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 620 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 256
 h1 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 67 h1 (* h2 h2 h2
) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 302 h1 (* h2 h2 h2) (* 
h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 456 h1 (* h2 h2 h2) (* h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6
 h6) (* j2 j2 j2 j2)) (* 12 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 48 h1 (* h2 h2 h2) (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6
 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2
 h2 h2) (* h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 13 h1 (* h2 h2 h2) (* 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 160 h1 (* h2 h2 h2) (* h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 43 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2
 j2 j2 j2 j2)) (* 201 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 300 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 128 h1 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 31
 h1 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 124 h1 
(* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 164 h1 (* h2 h2
 h2) (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2 h2) (* h3 
h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) (* h3 h3) (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 
j2)) (* 22 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
16 h1 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 5 h1 (* h2 
h2 h2) h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) h3 
(* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2) h3 (* h4 h4) (* 
h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2)) (* 22 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2)) (* 75 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 48 h1 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 h1 (* 
h2 h2 h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2 
h2) h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) h3 h4 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2 h2) h3 h4 (* h5 h5 
h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 17 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 65 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2)) (* 32 h1 (* h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 35 h1
 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 84 h1 (* h2
 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2 h2) 
h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 15 h1 (* h2 h2 h2) h3 h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2 h2) h3 h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2
 j2 j2 j2)) (* 8 h1 (* h2 h2 h2) h3 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 13 h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 33 
h1 (* h2 h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 
h2 h2) h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h3 
(* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 31 h1 (* h2 h2 h2) h3 (* h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2 h2) h3 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 5 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2 h2) h3 h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2
)) (* h1 (* h2 h2 h2) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 
h1 (* h2 h2 h2) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* 
h2 h2 h2) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2
 h2) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2 h2) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2 h2) h4 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) (* h5 h5 h5 h5) (* h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2 h2) (* h5 h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2 h2) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 180 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2
 j2)) (* 1040 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) 
(* 2448 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 2432 h1
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* 
h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 16 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4
 h4) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2 j2 j2 j2)) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2
 j2 j2 j2 j2)) (* 256 h1 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2))
 (* 4 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
118 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 844 
h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2336 h1 (* 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2560 h1 (* h2 h2) (* 
h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) 
h4 (* h5 h5) (* j2 j2 j2)) (* 32 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 464 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 
j2 j2 j2)) (* 2320 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 5120 h1 (* h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 4928 h1 (* 
h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 1536 h1 (* h2 h2) (* h3 h3 
h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 32 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 1024 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 512 h1 (* h2 h2) (* h3 h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 12 
h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 120 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2
) (* h3 h3 h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2) (* h3 h3 
h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 138 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 828 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 2160 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 2368 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2))
 (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 24 h1 (* h2 
h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 284 h1 (* h2 h2
) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1280 h1 (* h2 h2) 
(* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2672 h1 (* h2 h2) (* h3 
h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2496 h1 (* h2 h2) (* h3 h3 h3 h3) 
h5 (* h6 h6) (* j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2)) (* 16 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 128 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2
 j2)) (* 384 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 512 h1 (* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 256 h1 
(* h2 h2) (* h3 h3 h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h1 (* h2 h2) (* h3 
h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 126 h1 (* h2 h2) (* h3 h3
 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 532 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 816 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4
 h4) h5 (* j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* 
j2 j2 j2 j2)) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 96 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2 j2)) (* 
64 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h6 (* j2 j2 j2 j2 j2)) (* 21 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 320 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 1288 h1 (* 
h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1856 h1 (* h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* 
h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 64 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 578 h1 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1916 h1 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 2608 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 1152 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 (* 
j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2 j2)) (* 144 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 288 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 
j2 j2 j2)) (* 192 h1 (* h2 h2) (* h3 h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 7 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 130 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
640 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 1024 h1 
(* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 68 h1 (* h2 h2) (* h3 h3 h3) h4
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 746 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2652 h1 (* h2 h2) (* h3 h3 h3) h4 (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 3648 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2 j2)) (* 1536 h1 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 104 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 778 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 2236 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 2768 h1 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1152 h1
 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 24 h1 (* h2 h2) (* 
h3 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h2 h2) (* h3
 h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h2 h2) (* h3 h3 
h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2) (* h3 h3 h3) h4 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2)) (* 11 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 142 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
600 h1 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 928 h1 
(* h2 h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 384 h1 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 47 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 426 h1 (* h2 h2) (* h3 h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1364 h1 (* h2 h2) (* h3 h3 h3
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1792 h1 (* h2 h2) (* h3 h3 h3) 
(* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 768 h1 (* h2 h2) (* h3 h3 h3) (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 326 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 852 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 976 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 
j2 j2)) (* 384 h1 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 
h1 (* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 
(* h2 h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 (* h2 
h2) (* h3 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2) (* h3
 h3 h3) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) (* h3 h3) (* h4 h4
 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 36 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4
) h5 (* j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5 (* 
j2 j2 j2 j2 j2)) (* 10 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2 j2 j2)) (* 114 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 296 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 192 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 
j2 j2)) (* 16 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 82 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 196 h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 192 
h1 (* h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 13 h1 (* h2 h2)
 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 147 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 356 h1 (* h2 
h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2) 
(* h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 63 h1 (* h2 h2) (* h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 434 h1 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 936 h1 (* h2 h2) (* h3 
h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) (* h4 h4
) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 210 h1 (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 372 h1 (* h2 h2) (* h3 h3) (* h4 
h4) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h2 h2) (* h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 30 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 100 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2
)) (* 39 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 321 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
696 h1 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 384 h1 
(* h2 h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 96 h1 (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 526 h1 (* h2 h2
) (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 984 h1 (* h2 h2)
 (* h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 576 h1 (* h2 h2) (* 
h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 198 h1 (* h2 h2) (* h3 h3) h4
 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 300 h1 (* h2 h2) (* h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 h2) (* h3 h3) h4 h5 (* h6 h6
 h6) (* j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 31 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2
 j2 j2 j2 j2)) (* 88 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2)) (* 48 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 26 
h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
174 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
340 h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 
h1 (* h2 h2) (* h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 43 h1 (* h2
 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 206 h1 (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 344 h1 (* 
h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 h1 (* h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 h1 (* h2 h2) (* 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h2 h2) (* h3 
h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 88 h1 (* h2 h2) (* h3 h3) h5
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) (* h3 h3) h5 (* h6 h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2
 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2
 j2 j2 j2)) (* 3 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 24 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)
) (* 24 h1 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 h1
 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 25 h1 
(* h2 h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 
h2) h3 (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) h3 (* 
h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 17 h1 (* h2 h2) h3 (* h4 
h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h4 h4) 
(* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 19 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 82 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 57 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 6 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 35 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 24 h1 (* h2 h2) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 29 h1 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 (* h2 
h2) h3 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 h1 (* h2 h2) h3
 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h2 h2) h3 h4 (* h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 51 h1 (* h2 h2) h3 h4 (* h5 h5
) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 (* h2 h2) h3 h4 (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 13 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2)) (* 34 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 24 h1 (* h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8
 h1 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1
 (* h2 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h2
 h2) h3 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2) (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2) (* h4 h4) 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) (* h4 h4) (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 (* h2 h2) h4 (* h5 h5 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 3 h1 (* h2 h2) h4 (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2) (* h5 h5 h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h2 h2) (* h5 h5 h5) (* h6 h6 h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 160 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 576 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)
) (* 896 h1 h2 (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 512 h1 h2 
(* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 2 h1 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 90 h1 h2 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 708 h1 h2 (* h3 h3 h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2096 h1 h2 (* h3 h3 h3 h3) (* h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2560 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 
h5) (* j2 j2 j2 j2 j2)) (* 1024 h1 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 
j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 200 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 1008 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
2528 h1 h2 (* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 3136 h1 h2 
(* h3 h3 h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 1536 h1 h2 (* h3 h3 h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 26 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 276 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 992 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 1344 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 512
 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 12 h1 h2 (* h3 h3 h3 
h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 248 h1 h2 (* h3 h3 h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1608 h1 h2 (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 4400 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2 j2 j2 j2)) (* 5184 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 
j2 j2 j2 j2)) (* 2048 h1 h2 (* h3 h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 
32 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 352 
h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1536 h1 h2
 (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 3328 h1 h2 (* h3 
h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3584 h1 h2 (* h3 h3 h3 h3) 
h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 1536 h1 h2 (* h3 h3 h3 h3) h4 h5 (* h6 h6
) (* j2 j2 j2 j2)) (* 24 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 256 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 928 h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1280 
h1 h2 (* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 
h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 10 h1 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 158 h1 h2 (* h3 h3 h3 h3) (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 900 h1 h2 (* h3 h3 h3 h3) (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2304 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2624 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2)) (* 1024 h1 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 16 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 168 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 688 h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1376 
h1 h2 (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1344 h1 h2 (* h3
 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3 h3) h5 
(* h6 h6 h6) (* j2 j2 j2 j2)) (* 8 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 
j2 j2 j2 j2)) (* 160 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)
) (* 128 h1 h2 (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 3 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 83 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 484 h1 h2 
(* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 928 h1 h2 (* h3
 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 8 h1 h2 (* h3 h3 h3) (* h4 h4 h4) 
h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 400 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 752 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 
j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 4
 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
100 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
552 h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 992 
h1 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 512 h1 h2 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 33 h1 h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 407 h1 h2 (* h3 h3 h3
) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1752 h1 h2 (* h3 h3 h3)
 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2944 h1 h2 (* h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1536 h1 h2 (* h3 h3 h3) (* h4 h4) 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 24 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6)
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 228 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 816 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 1296 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 768 h1 h2 (* h3 h3 h3) (* h4 h4) h5 (* h6 h6) (* j2 j2 j2
 j2 j2)) (* 13 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 112 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 272 
h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 16 h1 h2 (* h3 h3 h3) h4 (* h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 252 h1 h2 (* h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1192 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2016 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2
 j2 j2 j2 j2 j2)) (* 1024 h1 h2 (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2)) (* 57 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 565 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 2052 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3104 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 1536
 h1 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 24 h1 h2 (* h3
 h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 212 h1 h2 (* h3 h3
 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 688 h1 h2 (* h3 h3 h3) 
h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 976 h1 h2 (* h3 h3 h3) h4 h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 12 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 104 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2)) (* 256 h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 128 
h1 h2 (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 12 h1 h2 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 152 h1 h2 (* h3 h3
 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 640 h1 h2 (* h3 h3 
h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1024 h1 h2 (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3) (* h5 h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 27 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 241 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6
 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 784 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1088 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 512 h1 h2 (* h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2
 j2 j2 j2)) (* 8 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 68 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 208 h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 272 
h1 h2 (* h3 h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 
h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 8 h1 h2 (* h3 h3) (* h4 h4 h4 
h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h1 h2 (* h3 h3) (* h4 h4 h4 h4)
 (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 h2 (* h3 h3) (* h4 h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 41 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 164 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 
j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2
 j2 j2 j2)) (* 9 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 79 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 244 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2
)) (* 256 h1 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* h1
 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 23 h1
 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 h2
 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 h2 (* h3
 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 18 h1 h2 (* h3 h3) (* 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 178 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 532 h1 h2 (* h3 h3) 
(* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 h2 (* h3 h3) (* h4
 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 27 h1 h2 (* h3 h3) (* h4 h4) (* 
h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 189 h1 h2 (* h3 h3) (* h4 h4
) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 444 h1 h2 (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 h2 (* h3 h3) (* h4 
h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 h2 (* h3 h3) h4 (* h5 h5 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55 h1 h2 (* h3 h3) h4 (* h5 h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 188 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 30 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2 j2)) (* 233 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 572 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2)) (* 384 h1 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2))
 (* 27 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 173 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 348 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
256 h1 h2 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 3 h1 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 h2 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 h2 (* h3 h3)
 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 14 h1 h2 (* h3 h3) (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 h1 h2 (* h3 h3) (* h5 h5
 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 204 h1 h2 (* h3 h3) (* h5 h5 
h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 h2 (* h3 h3) (* h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 9 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 55 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 
h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 100 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 h2 (* h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 8 h1 h2 h3 (* h4 h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2))
 (* 2 h1 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1
 h2 h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3 (* 
h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 15 h1 h2 h3 (* h4 
h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 h2 h3 (* h4 h4 h4) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5
) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 13 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 h1 h2 h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2)) (* 6 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 33 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 48 h1 h2 h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 4 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 20 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 24 h1 h2 h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 h2
 h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 29 h1 h2 h3 
h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h1 h2 h3 h4 (* 
h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3 (* h5 h5 h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 9 h1 h2 h3 (* h5 h5 h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 h2 h3 (* h5 h5 h5 h5) (* h6 h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 2 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2
 j2 j2 j2 j2 j2 j2)) (* 9 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 8 h1 h2 h3 (* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2
)) (* 4 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 48 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 208 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
384 h1 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 256 h1 
(* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h3 h3 h3 h3
) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 320 h1 (* h3 h3 h3 h3) (* 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 256 h1 (* h3 h3 h3 h3) (* h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 32 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6
 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 304 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1024 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1472 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 
(* j2 j2 j2 j2 j2 j2)) (* 768 h1 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 14 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2 j2)) (* 156 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 608 h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 960 
h1 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 512 h1 (* h3 h3 
h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 52 h1 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 464 h1 (* h3 h3 h3 h3) h4 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 1424 h1 (* h3 h3 h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1792 h1 (* h3 h3 h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 768 h1 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2 j2)) (* 12 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 464 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 640 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 256 h1 (* h3 h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 24 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 208 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 608 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
704 h1 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 h1 
(* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 2 h1 (* h3 h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h1 (* h3 h3 h3) 
(* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h3 h3 h3) (* 
h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h3 h3 h3) (* h4 h4 
h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 18 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 140 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2 j2 j2)) (* 336 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 256 h1 (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2
 j2 j2)) (* h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
 j2)) (* 12 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2
)) (* 48 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 
64 h1 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 32 h1 (* 
h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 544 h1 
(* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h3
 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 42 h1 (* h3 h3 h3) 
(* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 300 h1 (* h3 h3
 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 624 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h3 
h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 h1 (* h3 h3 h3)
 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h3 h3 h3) h4 
(* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 176 h1 (* h3 h3 h3) h4 (* h5 
h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h3 h3 h3) h4 (* h5 h5 h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* 52 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2 j2 j2)) (* 360 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 704 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 384 h1 (* h3 h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 38 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 260 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 496 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 256 h1 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) 
(* 6 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 52 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
128 h1 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1
 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24 h1 (* h3 h3
 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 160 h1 (* h3 
h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 h1 (* h3 h3
 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h1 (* h3 h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 h1 (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h1 (* h3 h3 h3) (* h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h1 (* h3 h3 h3) (* h5 h5) 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* h3 h3 h3) (* h5 h5) (* h6 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4 h4 h4) (* h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2 j2)) (* 8 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 9 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 52 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 64 h1 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)
) (* 8 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 44 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 48 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 21 
h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 108 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 96 h1 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 13 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 64 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
48 h1 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 19 h1 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 92 h1 
(* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h1 (* 
h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3) 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 6 h1 (* h3 h3) (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h1 (* h3 h3) (* h5 h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h1 (* h3 h3) (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3 h3) (* 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5
 (* j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2
 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 2 (* h2 
h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 20 (* h2 h2 h2 h2)
 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3
) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) 
(* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2)) (* 160 (* h2 h2 
h2 h2) (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 128 (* h2 h2 h2 h2) (* h3 h3 h3
) h4 h5 h6 (* j2 j2 j2)) (* 2 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2
 j2 j2 j2 j2)) (* 20 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2
)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 64 (* h2 
h2 h2 h2) (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3 
h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3 h3) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 80 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) 
(* j2 j2 j2 j2)) (* 64 (* h2 h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2)) 
(* 2 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 12 (* 
h2 h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2 h2)
 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2) (* h3 h3) (* h4
 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) 
(* h5 h5) (* j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) (* h5 h5
) (* j2 j2 j2 j2)) (* 6 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2
 j2 j2)) (* 36 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 
48 (* h2 h2 h2 h2) (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* (* h2 h2 h2 h2)
 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3)
 h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5
 h5) (* j2 j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2
 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) 
(* 64 (* h2 h2 h2 h2) (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 6 (* h2 h2 
h2 h2) (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 36 (* h2 h2 h2 h2) 
(* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2 h2) (* h3 h3) h4
 h5 (* h6 h6) (* j2 j2 j2 j2)) (* (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4 
(* h2 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 24 (* h2
 h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 32 (* h2 h2 h2 
h2) (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 2 (* h2 h2 h2 h2) (* h3 h3
) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2 h2) (* h3 h3) h5 (* 
h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2 j2)) (* (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 
j2)) (* 4 (* h2 h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* (* h2
 h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2)
 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 3 (* h2 h2 h2 h2) h3 (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2 h2) h3 (* h4 h4) (* h5 h5
) h6 (* j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 8 (* h2 h2 h2 h2) h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 3 
(* h2 h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 
h2 h2) h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) h3 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2 h2) h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 80 (* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 288 
(* h2 h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2 j2)) (* 448 (* h2 h2 h2
) (* h3 h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h5 (* j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 
j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 384 (* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 256 
(* h2 h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 16 (* h2 h2 h2) (* h3
 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 160 (* h2 h2 h2) (* h3 h3 h3 h3
) h4 h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 576 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 
(* j2 j2 j2 j2 j2)) (* 896 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)
) (* 512 (* h2 h2 h2) (* h3 h3 h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 4 (* h2 h2 h2) 
(* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 
h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 208 (* h2 h2 h2) (* h3 h3 h3 h3
) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5)
 h6 (* j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3 h3) (* h5 h5) h6 (* j2 j2 
j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 80 (* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 288 
(* h2 h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 448 (* h2 h2 h2
) (* h3 h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3 
h3) h5 (* h6 h6) (* j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 
j2 j2 j2 j2 j2)) (* 160 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2
 j2)) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 14 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 116 
(* h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 304 (* 
h2 h2 h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 256 (* h2 h2 
h2) (* h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 24 (* h2 h2 h2) (* h3 
h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3 h3
) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 384 (* h2 h2 h2) (* h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 40 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)
) (* 128 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 128 
(* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 28 (* h2 h2 h2) 
(* h3 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 232 (* h2 h2 h2) (* h3
 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 608 (* h2 h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2 h2) (* h3 h3 h3) h4 (* h5 h5
) h6 (* j2 j2 j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2)) (* 480 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) 
(* 384 (* h2 h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2 
h2) (* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 40 (* h2 h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3
 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3 h3) (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 14 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 304 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 256 (* h2 h2 h2) (* h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))
 (* 64 (* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 160 
(* h2 h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2
) (* h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h2 h2 h2) (* h3 h3) (* 
h4 h4 h4 h4) h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) (* h3 h3) (* h4 h4 
h4 h4) h5 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4 h4) h5
 (* j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2
 j2)) (* 8 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 48 (* h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 64 (* 
h2 h2 h2) (* h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2) (* 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2 h2) (* h3
 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3) (* h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h2 h2 h2) (* h3 h3) (* h4 h4)
 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3) (* h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2 j2 j2 j2 j2)) (* 72 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) 
(* j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2 h2) (* h3 h3) (* h4 h4) h5 (* h6 h6) (* j2
 j2 j2 j2 j2)) (* (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2
 j2)) (* 8 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
16 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 14 (* h2 h2 
h2) (* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 88 (* h2 h2 h2) 
(* h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2 h2) (* h3 h3
) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h2 h2 h2) (* h3 h3) h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2 h2) (* h3 h3) h4 (* h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)
) (* (* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 
(* h2 h2 h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2 
h2) (* h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 7 (* h2 h2 h2) (* h3 h3)
 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2 h2) (* h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* 
h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 48 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2 h2) (* h3 h3) (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 12 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* 16 (* h2 h2 h2) (* h3 h3) h5 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
(* h2 h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 
h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2) h3 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) h3 (* h4 
h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2) h3 (* h4 h4 h4) (* h5 h5)
 h6 (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 6 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2))
 (* 24 (* h2 h2 h2) h3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* 
h2 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2
 h2 h2) h3 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2 h2
) h3 h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2) h3 h4 (* 
h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 6 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6)
 (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2 j2)) (* 16 (* h2 h2 h2) h3 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 
j2 j2)) (* (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 4 (* h2 h2 h2) h3 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2
 h2 h2) h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2 h2)
 h3 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2 h2) h3 (* h5 h5
) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2 h2) h3 (* h5 h5) (* h6
 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5
 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2 j2)) (* 288 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2
 j2 j2 j2 j2 j2)) (* 448 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 
j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4 h4) h5 (* j2 j2 j2 j2)) (* 8 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96
 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 416 
(* h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 768 (* 
h2 h2) (* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 512 (* h2 h2) 
(* h3 h3 h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3
 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 240 (* h2 h2) (* h3 h3 h3 
h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 864 (* h2 h2) (* h3 h3 h3 h3) 
(* h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 1344 (* h2 h2) (* h3 h3 h3 h3) (* h4 
h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 28 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 
j2 j2)) (* 144 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 320 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 256 (* 
h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 16 (* h2 h2) (* h3 h3
 h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3 
h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 832 (* h2 h2) (* h3 h3 h3 h3
) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 1536 (* h2 h2) (* h3 h3 h3 h3) h4 
(* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 1024 (* h2 h2) (* h3 h3 h3 h3) h4 (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2 j2)) (* 240 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2 j2 j2)) (* 864 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 1344 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 
768 (* h2 h2) (* h3 h3 h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 2 (* h2 h2) 
(* h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 (* h2 h2) (* 
h3 h3 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 144 (* h2 h2) (* h3 h3
 h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 320 (* h2 h2) (* h3 h3 h3 h3) 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5 h5
) h6 (* j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 416 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 
j2 j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2)) (* 512 (* h2 h2) (* h3 h3 h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2))
 (* 8 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
80 (* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 288 
(* h2 h2) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 448 (* h2 h2
) (* h3 h3 h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3 
h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 
h4) h5 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4)
 h5 (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 
(* j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4 h4) h5 (* j2 j2 
j2 j2 j2)) (* 14 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 116 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2 j2)) (* 304 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2))
 (* 16 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 128 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 
320 (* h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2 j2)) (* 256 (* 
h2 h2) (* h3 h3 h3) (* h4 h4 h4) h5 h6 (* j2 j2 j2 j2 j2)) (* 8 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2) (* h3
 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 
h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3 
h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 42 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 348 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 912 (* h2 h2) (* h3 h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3) (* 
h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3) (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 h2) (* h3 h3 h3) (* h4 h4
) h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 480 (* h2 h2) (* h3 h3 h3) (* h4 h4)
 h5 (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 384 (* h2 h2) (* h3 h3 h3) (* h4 h4) h5 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2
 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 
16 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 160
 (* h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 512 (* 
h2 h2) (* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 512 (* h2 h2) 
(* h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 42 (* h2 h2) (* h3 h3 h3)
 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 348 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 912 (* h2 h2) (* h3 h3 
h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 768 (* h2 h2) (* h3 h3 h3) 
h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 16 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2) (* h3 h3 h3) h4 h5 
(* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 320 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3 h3) h4 h5 (* h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 48 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 64 (* h2 h2) (* h3 h3 h3) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 8 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h2
 h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 (* h2 
h2) (* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2) 
(* h3 h3 h3) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 14 (* h2 h2) (* h3 h3
 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 116 (* h2 h2) (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 304 (* h2 h2) (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 (* h2 h2) (* h3 h3 
h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3 h3) h5 
(* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3 h3) h5 (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 80 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 
h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3 h3) h5 (* h6 h6 h6 h6) 
(* j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 7 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 44 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2
 j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 
j2 j2)) (* 16 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2
 j2 j2)) (* 96 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 128 (* h2 h2) (* h3 h3) (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 
j2)) (* 2 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 16 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 32 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) 
(* 21 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 132 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 
24 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 144 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2)) (* 192 (* h2 h2) (* h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2))
 (* 32 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 64
 (* h2 h2) (* h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 21 (* h2 h2
) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 132 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 192 (* h2 
h2) (* h3 h3) h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 (* h2 h2)
 (* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 (* h2 h2) 
(* h3 h3) h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 (* h2 h2) (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 h2) (* h3
 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2) (* h3 
h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 7 (* h2 h2) (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 44 (* h2 h2) (* h3 h3)
 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 (* h2 h2) (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3) (* h5
 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 32 (* h2 h2) (* h3 h3) (* h5 
h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 (* h4 h4 h4 h4) (* h5
 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4 h4) (* h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2
 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 3 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 
j2)) (* 12 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) 
(* 6 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 24 (* h2 h2) h3 (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) 
(* 3 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
12 (* h2 h2) h3 h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 (* 
h2 h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 (* h2 
h2) h3 h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 
(* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* 
h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* (* h2 h2) h3 (* h5 h5 h5)
 (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* 
h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5
 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) 
(* j2 j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h4 h4 h4) (* h5 h5) (* j2 j2
 j2 j2 j2)) (* 2 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 28 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 144 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2
)) (* 320 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 
256 h2 (* h3 h3 h3 h3) (* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 12 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h2 (* 
h3 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 624 h2 (* h3
 h3 h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 1152 h2 (* h3 h3 
h3 h3) (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 768 h2 (* h3 h3 h3 h3) 
(* h4 h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3 h3) h4 (* h5 h5 
h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 56 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) 
h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 288 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* 
j2 j2 j2 j2 j2 j2 j2)) (* 640 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 
j2 j2 j2)) (* 512 h2 (* h3 h3 h3 h3) h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 
12 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 
144 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 
624 h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 1152 
h2 (* h3 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 768 h2 (* h3
 h3 h3 h3) h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 2 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 28 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 144 h2 (* h3 h3 h3 h3) 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 320 h2 (* h3 h3 h3 h3) (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 208 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2 j2 j2 j2 j2)) (* 384 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 
j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3 h3) (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2
)) (* 2 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)
) (* 20 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 64 h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 
h2 (* h3 h3 h3) (* h4 h4 h4 h4) (* h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 40 h2 (* h3 
h3 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3
 h3) (* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 h3 h3) 
(* h4 h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h2 (* h3 h3 h3) (* h4 h4 
h4) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3) (* h4 h4 h4
) (* h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3) (* h4 h4 h4) (* 
h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) 
(* j2 j2 j2 j2 j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* 
j2 j2 j2 j2 j2 j2 j2)) (* 64 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5 h5) (* j2 j2 
j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2 j2 j2)) (* 120 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) 
(* 12 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 120 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2 j2)) (* 384 h2 (* h3 h3 h3) (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 2 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 24 h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 96 
h2 (* h3 h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2 j2)) (* 128 h2 (* h3 
h3 h3) h4 (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3) h4 (* 
h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 120 h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 384 h2 (* h3 h3 h3) h4 
(* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 384 h2 (* h3 h3 h3) h4 (* h5
 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 80 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6
 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 
h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 256 h2 (* h3 h3 h3) h4 (* h5 h5) (* h6 h6 h6
) (* j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2 j2)) (* 12 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 
j2 j2 j2 j2 j2 j2)) (* 48 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2 j2 j2)) (* 64 h2 (* h3 h3 h3) (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 
j2)) (* 4 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 
j2)) (* 40 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)
) (* 128 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 
128 h2 (* h3 h3 h3) (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* 2 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 20 h2 (* 
h3 h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 64 h2 (* h3 
h3 h3) (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* 64 h2 (* h3 h3 h3)
 (* h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3) (* h4 h4 h4 h4
) (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3) (* h4 h4 h4 h4)
 (* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4 h4) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 
h5) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5 h5)
 (* j2 j2 j2 j2 j2 j2 j2)) (* 4 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2 j2)) (* 32 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 
j2 j2 j2 j2 j2 j2 j2)) (* 64 h2 (* h3 h3) (* h4 h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2 j2 j2 j2)) (* 3 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2 j2)) (* 24 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 
j2 j2 j2 j2)) (* 48 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5 h5) h6 (* j2 j2 j2 j2 j2 
j2 j2)) (* 6 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 48 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2
 j2 j2 j2)) (* 96 h2 (* h3 h3) (* h4 h4) (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 
j2 j2 j2)) (* 3 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2 j2)) (* 24 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 
j2 j2)) (* 48 h2 (* h3 h3) h4 (* h5 h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2 j2 j2)
) (* 4 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2))
 (* 32 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) 
(* 64 h2 (* h3 h3) h4 (* h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h2 
(* h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h2 (* 
h3 h3) (* h5 h5 h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2)) (* h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2 j2)) (* 8 h2 (* h3 h3) 
(* h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2 j2)) (* 16 h2 (* h3 h3) (* 
h5 h5 h5) (* h6 h6 h6 h6) (* j2 j2 j2 j2 j2 j2 j2))) 0)))
(check-sat)
(exit)
