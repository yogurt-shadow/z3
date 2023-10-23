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
(set-info :instance |E14E26|)
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
(+ (* 4 (* h1 h1 h1) (* h2 h2) h3 j2) (- (* 2 (* h1 h1 h1) (* h2 h2) h3)) (* 2 
(* h1 h1 h1) (* h2 h2) h5 j2) (* 2 (* h1 h1 h1) (* h2 h2) h5) (* 2 (* h1 h1 h1) 
(* h2 h2) h6 j2) (* 16 (* h1 h1 h1) h2 (* h3 h3) (* j2 j2)) (* 8 (* h1 h1 h1) h2
 (* h3 h3) j2) (- (* 8 (* h1 h1 h1) h2 (* h3 h3))) (* 8 (* h1 h1 h1) h2 h3 h4 j2
) (* 4 (* h1 h1 h1) h2 h3 h4) (* 16 (* h1 h1 h1) h2 h3 h5 (* j2 j2)) (* 26 (* h1
 h1 h1) h2 h3 h5 j2) (* 10 (* h1 h1 h1) h2 h3 h5) (* 16 (* h1 h1 h1) h2 h3 h6 
(* j2 j2)) (* 28 (* h1 h1 h1) h2 h3 h6 j2) (* 10 (* h1 h1 h1) h2 h3 h6) (* 4 (* 
h1 h1 h1) h2 h4 h5 j2) (* 2 (* h1 h1 h1) h2 h4 h5) (* 4 (* h1 h1 h1) h2 h4 h6 j2
) (* 4 (* h1 h1 h1) h2 (* h5 h5) (* j2 j2)) (* 6 (* h1 h1 h1) h2 (* h5 h5) j2) 
(* 2 (* h1 h1 h1) h2 (* h5 h5)) (* 8 (* h1 h1 h1) h2 h5 h6 (* j2 j2)) (* 6 (* h1
 h1 h1) h2 h5 h6 j2) (* 4 (* h1 h1 h1) h2 (* h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1)
 h2 (* h6 h6) j2) (* 16 (* h1 h1 h1) (* h3 h3) h4 (* j2 j2)) (* 40 (* h1 h1 h1) 
(* h3 h3) h4 j2) (* 24 (* h1 h1 h1) (* h3 h3) h4) (* 16 (* h1 h1 h1) (* h3 h3) 
h5 (* j2 j2 j2)) (* 72 (* h1 h1 h1) (* h3 h3) h5 (* j2 j2)) (* 72 (* h1 h1 h1) 
(* h3 h3) h5 j2) (* 16 (* h1 h1 h1) (* h3 h3) h5) (* 32 (* h1 h1 h1) (* h3 h3) 
h6 (* j2 j2 j2)) (* 80 (* h1 h1 h1) (* h3 h3) h6 (* j2 j2)) (* 64 (* h1 h1 h1) 
(* h3 h3) h6 j2) (* 16 (* h1 h1 h1) (* h3 h3) h6) (* 4 (* h1 h1 h1) h3 (* h4 h4)
 j2) (* 6 (* h1 h1 h1) h3 (* h4 h4)) (* 16 (* h1 h1 h1) h3 h4 h5 (* j2 j2)) (* 
26 (* h1 h1 h1) h3 h4 h5 j2) (* 6 (* h1 h1 h1) h3 h4 h5) (* 16 (* h1 h1 h1) h3 
h4 h6 (* j2 j2)) (* 28 (* h1 h1 h1) h3 h4 h6 j2) (* 10 (* h1 h1 h1) h3 h4 h6) 
(* 8 (* h1 h1 h1) h3 (* h5 h5) (* j2 j2 j2)) (* 32 (* h1 h1 h1) h3 (* h5 h5) (* 
j2 j2)) (* 22 (* h1 h1 h1) h3 (* h5 h5) j2) (* 4 (* h1 h1 h1) h3 (* h5 h5)) (* 
40 (* h1 h1 h1) h3 h5 h6 (* j2 j2 j2)) (* 72 (* h1 h1 h1) h3 h5 h6 (* j2 j2)) 
(* 42 (* h1 h1 h1) h3 h5 h6 j2) (* 8 (* h1 h1 h1) h3 h5 h6) (* 16 (* h1 h1 h1) 
h3 (* h6 h6) (* j2 j2 j2)) (* 32 (* h1 h1 h1) h3 (* h6 h6) (* j2 j2)) (* 20 (* 
h1 h1 h1) h3 (* h6 h6) j2) (* 4 (* h1 h1 h1) h3 (* h6 h6)) (* 2 (* h1 h1 h1) (* 
h4 h4) h5 j2) (* 2 (* h1 h1 h1) (* h4 h4) h6 j2) (* 4 (* h1 h1 h1) h4 (* h5 h5) 
(* j2 j2)) (* 2 (* h1 h1 h1) h4 (* h5 h5) j2) (* 8 (* h1 h1 h1) h4 h5 h6 (* j2 
j2)) (* 10 (* h1 h1 h1) h4 h5 h6 j2) (* 2 (* h1 h1 h1) h4 h5 h6) (* 4 (* h1 h1 
h1) h4 (* h6 h6) (* j2 j2)) (* 2 (* h1 h1 h1) h4 (* h6 h6) j2) (* 8 (* h1 h1 h1)
 (* h5 h5) h6 (* j2 j2 j2)) (* 16 (* h1 h1 h1) (* h5 h5) h6 (* j2 j2)) (* 10 (* 
h1 h1 h1) (* h5 h5) h6 j2) (* 2 (* h1 h1 h1) (* h5 h5) h6) (* 8 (* h1 h1 h1) h5 
(* h6 h6) (* j2 j2 j2)) (* 16 (* h1 h1 h1) h5 (* h6 h6) (* j2 j2)) (* 10 (* h1 
h1 h1) h5 (* h6 h6) j2) (* 2 (* h1 h1 h1) h5 (* h6 h6)) (* 2 (* h1 h1) (* h2 h2 
h2) h3 j2) (- (* (* h1 h1) (* h2 h2 h2) h3)) (* (* h1 h1) (* h2 h2 h2) h5 j2) 
(* (* h1 h1) (* h2 h2 h2) h5) (* (* h1 h1) (* h2 h2 h2) h6 j2) (* 16 (* h1 h1) 
(* h2 h2) (* h3 h3) (* j2 j2)) (* 10 (* h1 h1) (* h2 h2) (* h3 h3) j2) (- (* 9 
(* h1 h1) (* h2 h2) (* h3 h3))) (* 14 (* h1 h1) (* h2 h2) h3 h4 j2) (* (* h1 h1)
 (* h2 h2) h3 h4) (* 16 (* h1 h1) (* h2 h2) h3 h5 (* j2 j2)) (* 26 (* h1 h1) (* 
h2 h2) h3 h5 j2) (* 10 (* h1 h1) (* h2 h2) h3 h5) (* 16 (* h1 h1) (* h2 h2) h3 
h6 (* j2 j2)) (* 33 (* h1 h1) (* h2 h2) h3 h6 j2) (* 8 (* h1 h1) (* h2 h2) h3 h6
) (* 7 (* h1 h1) (* h2 h2) h4 h5 j2) (* 6 (* h1 h1) (* h2 h2) h4 h5) (* 7 (* h1 
h1) (* h2 h2) h4 h6 j2) (* 4 (* h1 h1) (* h2 h2) (* h5 h5) (* j2 j2)) (* 7 (* h1
 h1) (* h2 h2) (* h5 h5) j2) (* 3 (* h1 h1) (* h2 h2) (* h5 h5)) (* 8 (* h1 h1) 
(* h2 h2) h5 h6 (* j2 j2)) (* 10 (* h1 h1) (* h2 h2) h5 h6 j2) (* 3 (* h1 h1) 
(* h2 h2) h5 h6) (* 4 (* h1 h1) (* h2 h2) (* h6 h6) (* j2 j2)) (* 4 (* h1 h1) 
(* h2 h2) (* h6 h6) j2) (* 16 (* h1 h1) h2 (* h3 h3 h3) (* j2 j2 j2)) (* 24 (* 
h1 h1) h2 (* h3 h3 h3) (* j2 j2)) (- (* 8 (* h1 h1) h2 (* h3 h3 h3))) (* 48 (* 
h1 h1) h2 (* h3 h3) h4 (* j2 j2)) (* 72 (* h1 h1) h2 (* h3 h3) h4 j2) (* 28 (* 
h1 h1) h2 (* h3 h3) h4) (* 40 (* h1 h1) h2 (* h3 h3) h5 (* j2 j2 j2)) (* 128 (* 
h1 h1) h2 (* h3 h3) h5 (* j2 j2)) (* 120 (* h1 h1) h2 (* h3 h3) h5 j2) (* 26 (* 
h1 h1) h2 (* h3 h3) h5) (* 56 (* h1 h1) h2 (* h3 h3) h6 (* j2 j2 j2)) (* 164 (* 
h1 h1) h2 (* h3 h3) h6 (* j2 j2)) (* 142 (* h1 h1) h2 (* h3 h3) h6 j2) (* 34 (* 
h1 h1) h2 (* h3 h3) h6) (* 14 (* h1 h1) h2 h3 (* h4 h4) j2) (* 13 (* h1 h1) h2 
h3 (* h4 h4)) (* 48 (* h1 h1) h2 h3 h4 h5 (* j2 j2)) (* 86 (* h1 h1) h2 h3 h4 h5
 j2) (* 28 (* h1 h1) h2 h3 h4 h5) (* 48 (* h1 h1) h2 h3 h4 h6 (* j2 j2)) (* 84 
(* h1 h1) h2 h3 h4 h6 j2) (* 30 (* h1 h1) h2 h3 h4 h6) (* 20 (* h1 h1) h2 h3 (* 
h5 h5) (* j2 j2 j2)) (* 63 (* h1 h1) h2 h3 (* h5 h5) (* j2 j2)) (* 55 (* h1 h1) 
h2 h3 (* h5 h5) j2) (* 15 (* h1 h1) h2 h3 (* h5 h5)) (* 64 (* h1 h1) h2 h3 h5 h6
 (* j2 j2 j2)) (* 149 (* h1 h1) h2 h3 h5 h6 (* j2 j2)) (* 126 (* h1 h1) h2 h3 h5
 h6 j2) (* 32 (* h1 h1) h2 h3 h5 h6) (* 28 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2 j2
)) (* 76 (* h1 h1) h2 h3 (* h6 h6) (* j2 j2)) (* 65 (* h1 h1) h2 h3 (* h6 h6) j2
) (* 17 (* h1 h1) h2 h3 (* h6 h6)) (* 7 (* h1 h1) h2 (* h4 h4) h5 j2) (* 3 (* h1
 h1) h2 (* h4 h4) h5) (* 7 (* h1 h1) h2 (* h4 h4) h6 j2) (* 12 (* h1 h1) h2 h4 
(* h5 h5) (* j2 j2)) (* 17 (* h1 h1) h2 h4 (* h5 h5) j2) (* 6 (* h1 h1) h2 h4 
(* h5 h5)) (* 24 (* h1 h1) h2 h4 h5 h6 (* j2 j2)) (* 31 (* h1 h1) h2 h4 h5 h6 j2
) (* 6 (* h1 h1) h2 h4 h5 h6) (* 12 (* h1 h1) h2 h4 (* h6 h6) (* j2 j2)) (* 8 
(* h1 h1) h2 h4 (* h6 h6) j2) (* 2 (* h1 h1) h2 (* h5 h5 h5) (* j2 j2 j2)) (* 5 
(* h1 h1) h2 (* h5 h5 h5) (* j2 j2)) (* 4 (* h1 h1) h2 (* h5 h5 h5) j2) (* (* h1
 h1) h2 (* h5 h5 h5)) (* 14 (* h1 h1) h2 (* h5 h5) h6 (* j2 j2 j2)) (* 30 (* h1 
h1) h2 (* h5 h5) h6 (* j2 j2)) (* 20 (* h1 h1) h2 (* h5 h5) h6 j2) (* 4 (* h1 h1
) h2 (* h5 h5) h6) (* 14 (* h1 h1) h2 h5 (* h6 h6) (* j2 j2 j2)) (* 30 (* h1 h1)
 h2 h5 (* h6 h6) (* j2 j2)) (* 19 (* h1 h1) h2 h5 (* h6 h6) j2) (* 3 (* h1 h1) 
h2 h5 (* h6 h6)) (* 2 (* h1 h1) h2 (* h6 h6 h6) (* j2 j2 j2)) (* 3 (* h1 h1) h2 
(* h6 h6 h6) (* j2 j2)) (* (* h1 h1) h2 (* h6 h6 h6) j2) (* 16 (* h1 h1) (* h3 
h3 h3) h4 (* j2 j2 j2)) (* 56 (* h1 h1) (* h3 h3 h3) h4 (* j2 j2)) (* 64 (* h1 
h1) (* h3 h3 h3) h4 j2) (* 24 (* h1 h1) (* h3 h3 h3) h4) (* 16 (* h1 h1) (* h3 
h3 h3) h5 (* j2 j2 j2 j2)) (* 88 (* h1 h1) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 144 
(* h1 h1) (* h3 h3 h3) h5 (* j2 j2)) (* 88 (* h1 h1) (* h3 h3 h3) h5 j2) (* 16 
(* h1 h1) (* h3 h3 h3) h5) (* 32 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 
112 (* h1 h1) (* h3 h3 h3) h6 (* j2 j2 j2)) (* 144 (* h1 h1) (* h3 h3 h3) h6 (* 
j2 j2)) (* 80 (* h1 h1) (* h3 h3 h3) h6 j2) (* 16 (* h1 h1) (* h3 h3 h3) h6) (* 
16 (* h1 h1) (* h3 h3) (* h4 h4) (* j2 j2)) (* 38 (* h1 h1) (* h3 h3) (* h4 h4) 
j2) (* 21 (* h1 h1) (* h3 h3) (* h4 h4)) (* 40 (* h1 h1) (* h3 h3) h4 h5 (* j2 
j2 j2)) (* 148 (* h1 h1) (* h3 h3) h4 h5 (* j2 j2)) (* 150 (* h1 h1) (* h3 h3) 
h4 h5 j2) (* 46 (* h1 h1) (* h3 h3) h4 h5) (* 56 (* h1 h1) (* h3 h3) h4 h6 (* j2
 j2 j2)) (* 140 (* h1 h1) (* h3 h3) h4 h6 (* j2 j2)) (* 122 (* h1 h1) (* h3 h3) 
h4 h6 j2) (* 38 (* h1 h1) (* h3 h3) h4 h6) (* 16 (* h1 h1) (* h3 h3) (* h5 h5) 
(* j2 j2 j2 j2)) (* 86 (* h1 h1) (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 137 (* h1 
h1) (* h3 h3) (* h5 h5) (* j2 j2)) (* 86 (* h1 h1) (* h3 h3) (* h5 h5) j2) (* 16
 (* h1 h1) (* h3 h3) (* h5 h5)) (* 64 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2 j2))
 (* 220 (* h1 h1) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 306 (* h1 h1) (* h3 h3) h5 h6
 (* j2 j2)) (* 190 (* h1 h1) (* h3 h3) h5 h6 j2) (* 40 (* h1 h1) (* h3 h3) h5 h6
) (* 32 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 112 (* h1 h1) (* h3 h3
) (* h6 h6) (* j2 j2 j2)) (* 144 (* h1 h1) (* h3 h3) (* h6 h6) (* j2 j2)) (* 80 
(* h1 h1) (* h3 h3) (* h6 h6) j2) (* 16 (* h1 h1) (* h3 h3) (* h6 h6)) (* 2 (* 
h1 h1) h3 (* h4 h4 h4) j2) (* 3 (* h1 h1) h3 (* h4 h4 h4)) (* 16 (* h1 h1) h3 
(* h4 h4) h5 (* j2 j2)) (* 30 (* h1 h1) h3 (* h4 h4) h5 j2) (* 14 (* h1 h1) h3 
(* h4 h4) h5) (* 16 (* h1 h1) h3 (* h4 h4) h6 (* j2 j2)) (* 23 (* h1 h1) h3 (* 
h4 h4) h6 j2) (* 8 (* h1 h1) h3 (* h4 h4) h6) (* 20 (* h1 h1) h3 h4 (* h5 h5) 
(* j2 j2 j2)) (* 65 (* h1 h1) h3 h4 (* h5 h5) (* j2 j2)) (* 55 (* h1 h1) h3 h4 
(* h5 h5) j2) (* 11 (* h1 h1) h3 h4 (* h5 h5)) (* 64 (* h1 h1) h3 h4 h5 h6 (* j2
 j2 j2)) (* 137 (* h1 h1) h3 h4 h5 h6 (* j2 j2)) (* 104 (* h1 h1) h3 h4 h5 h6 j2
) (* 24 (* h1 h1) h3 h4 h5 h6) (* 28 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2 j2)) (* 
52 (* h1 h1) h3 h4 (* h6 h6) (* j2 j2)) (* 33 (* h1 h1) h3 h4 (* h6 h6) j2) (* 7
 (* h1 h1) h3 h4 (* h6 h6)) (* 4 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 
20 (* h1 h1) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 27 (* h1 h1) h3 (* h5 h5 h5) (* j2
 j2)) (* 13 (* h1 h1) h3 (* h5 h5 h5) j2) (* 2 (* h1 h1) h3 (* h5 h5 h5)) (* 32 
(* h1 h1) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 104 (* h1 h1) h3 (* h5 h5) h6 (* 
j2 j2 j2)) (* 126 (* h1 h1) h3 (* h5 h5) h6 (* j2 j2)) (* 66 (* h1 h1) h3 (* h5 
h5) h6 j2) (* 12 (* h1 h1) h3 (* h5 h5) h6) (* 36 (* h1 h1) h3 h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 112 (* h1 h1) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 129 (* h1 h1) h3
 h5 (* h6 h6) (* j2 j2)) (* 65 (* h1 h1) h3 h5 (* h6 h6) j2) (* 12 (* h1 h1) h3 
h5 (* h6 h6)) (* 8 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 24 (* h1 h1) h3
 (* h6 h6 h6) (* j2 j2 j2)) (* 26 (* h1 h1) h3 (* h6 h6 h6) (* j2 j2)) (* 12 (* 
h1 h1) h3 (* h6 h6 h6) j2) (* 2 (* h1 h1) h3 (* h6 h6 h6)) (* (* h1 h1) (* h4 h4
 h4) h5 j2) (* (* h1 h1) (* h4 h4 h4) h6 j2) (* 4 (* h1 h1) (* h4 h4) (* h5 h5) 
(* j2 j2)) (* 4 (* h1 h1) (* h4 h4) (* h5 h5) j2) (* 8 (* h1 h1) (* h4 h4) h5 h6
 (* j2 j2)) (* 11 (* h1 h1) (* h4 h4) h5 h6 j2) (* (* h1 h1) (* h4 h4) h5 h6) 
(* 4 (* h1 h1) (* h4 h4) (* h6 h6) (* j2 j2)) (* 2 (* h1 h1) (* h4 h4) (* h6 h6)
 j2) (* 2 (* h1 h1) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 3 (* h1 h1) h4 (* h5 h5 h5)
 (* j2 j2)) (* (* h1 h1) h4 (* h5 h5 h5) j2) (* 14 (* h1 h1) h4 (* h5 h5) h6 (* 
j2 j2 j2)) (* 32 (* h1 h1) h4 (* h5 h5) h6 (* j2 j2)) (* 22 (* h1 h1) h4 (* h5 
h5) h6 j2) (* 4 (* h1 h1) h4 (* h5 h5) h6) (* 14 (* h1 h1) h4 h5 (* h6 h6) (* j2
 j2 j2)) (* 28 (* h1 h1) h4 h5 (* h6 h6) (* j2 j2)) (* 16 (* h1 h1) h4 h5 (* h6 
h6) j2) (* 2 (* h1 h1) h4 h5 (* h6 h6)) (* 2 (* h1 h1) h4 (* h6 h6 h6) (* j2 j2 
j2)) (* 3 (* h1 h1) h4 (* h6 h6 h6) (* j2 j2)) (* (* h1 h1) h4 (* h6 h6 h6) j2) 
(* 4 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 12 (* h1 h1) (* h5 h5 h5) h6 
(* j2 j2 j2)) (* 13 (* h1 h1) (* h5 h5 h5) h6 (* j2 j2)) (* 6 (* h1 h1) (* h5 h5
 h5) h6 j2) (* (* h1 h1) (* h5 h5 h5) h6) (* 8 (* h1 h1) (* h5 h5) (* h6 h6) (* 
j2 j2 j2 j2)) (* 26 (* h1 h1) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 31 (* h1 h1) 
(* h5 h5) (* h6 h6) (* j2 j2)) (* 16 (* h1 h1) (* h5 h5) (* h6 h6) j2) (* 3 (* 
h1 h1) (* h5 h5) (* h6 h6)) (* 4 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
12 (* h1 h1) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 13 (* h1 h1) h5 (* h6 h6 h6) (* j2
 j2)) (* 6 (* h1 h1) h5 (* h6 h6 h6) j2) (* (* h1 h1) h5 (* h6 h6 h6)) (* 4 h1 
(* h2 h2 h2) (* h3 h3) (* j2 j2)) (- (* h1 (* h2 h2 h2) (* h3 h3))) (* 4 h1 (* 
h2 h2 h2) h3 h4 j2) (* 4 h1 (* h2 h2 h2) h3 h5 (* j2 j2)) (* 5 h1 (* h2 h2 h2) 
h3 h5 j2) (* h1 (* h2 h2 h2) h3 h5) (* 4 h1 (* h2 h2 h2) h3 h6 (* j2 j2)) (* 7 
h1 (* h2 h2 h2) h3 h6 j2) (* 2 h1 (* h2 h2 h2) h3 h6) (* 2 h1 (* h2 h2 h2) h4 h5
 j2) (* 2 h1 (* h2 h2 h2) h4 h5) (* 2 h1 (* h2 h2 h2) h4 h6 j2) (* h1 (* h2 h2 
h2) (* h5 h5) (* j2 j2)) (* 2 h1 (* h2 h2 h2) (* h5 h5) j2) (* h1 (* h2 h2 h2) 
(* h5 h5)) (* 2 h1 (* h2 h2 h2) h5 h6 (* j2 j2)) (* 3 h1 (* h2 h2 h2) h5 h6 j2) 
(* h1 (* h2 h2 h2) h5 h6) (* h1 (* h2 h2 h2) (* h6 h6) (* j2 j2)) (* h1 (* h2 h2
 h2) (* h6 h6) j2) (* 8 h1 (* h2 h2) (* h3 h3 h3) (* j2 j2 j2)) (* 8 h1 (* h2 h2
) (* h3 h3 h3) (* j2 j2)) (- (* 2 h1 (* h2 h2) (* h3 h3 h3) j2)) (- (* 2 h1 (* 
h2 h2) (* h3 h3 h3))) (* 28 h1 (* h2 h2) (* h3 h3) h4 (* j2 j2)) (* 38 h1 (* h2 
h2) (* h3 h3) h4 j2) (* 8 h1 (* h2 h2) (* h3 h3) h4) (* 20 h1 (* h2 h2) (* h3 h3
) h5 (* j2 j2 j2)) (* 57 h1 (* h2 h2) (* h3 h3) h5 (* j2 j2)) (* 40 h1 (* h2 h2)
 (* h3 h3) h5 j2) (* 9 h1 (* h2 h2) (* h3 h3) h5) (* 28 h1 (* h2 h2) (* h3 h3) 
h6 (* j2 j2 j2)) (* 76 h1 (* h2 h2) (* h3 h3) h6 (* j2 j2)) (* 63 h1 (* h2 h2) 
(* h3 h3) h6 j2) (* 15 h1 (* h2 h2) (* h3 h3) h6) (* 12 h1 (* h2 h2) h3 (* h4 h4
) j2) (* 6 h1 (* h2 h2) h3 (* h4 h4)) (* 28 h1 (* h2 h2) h3 h4 h5 (* j2 j2)) (* 
49 h1 (* h2 h2) h3 h4 h5 j2) (* 20 h1 (* h2 h2) h3 h4 h5) (* 28 h1 (* h2 h2) h3 
h4 h6 (* j2 j2)) (* 54 h1 (* h2 h2) h3 h4 h6 j2) (* 15 h1 (* h2 h2) h3 h4 h6) 
(* 10 h1 (* h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 32 h1 (* h2 h2) h3 (* h5 h5) 
(* j2 j2)) (* 30 h1 (* h2 h2) h3 (* h5 h5) j2) (* 8 h1 (* h2 h2) h3 (* h5 h5)) 
(* 32 h1 (* h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 81 h1 (* h2 h2) h3 h5 h6 (* j2 j2))
 (* 69 h1 (* h2 h2) h3 h5 h6 j2) (* 19 h1 (* h2 h2) h3 h5 h6) (* 14 h1 (* h2 h2)
 h3 (* h6 h6) (* j2 j2 j2)) (* 41 h1 (* h2 h2) h3 (* h6 h6) (* j2 j2)) (* 36 h1 
(* h2 h2) h3 (* h6 h6) j2) (* 9 h1 (* h2 h2) h3 (* h6 h6)) (* 6 h1 (* h2 h2) (* 
h4 h4) h5 j2) (* 5 h1 (* h2 h2) (* h4 h4) h5) (* 6 h1 (* h2 h2) (* h4 h4) h6 j2)
 (* 7 h1 (* h2 h2) h4 (* h5 h5) (* j2 j2)) (* 12 h1 (* h2 h2) h4 (* h5 h5) j2) 
(* 5 h1 (* h2 h2) h4 (* h5 h5)) (* 14 h1 (* h2 h2) h4 h5 h6 (* j2 j2)) (* 23 h1 
(* h2 h2) h4 h5 h6 j2) (* 9 h1 (* h2 h2) h4 h5 h6) (* 7 h1 (* h2 h2) h4 (* h6 h6
) (* j2 j2)) (* 7 h1 (* h2 h2) h4 (* h6 h6) j2) (* h1 (* h2 h2) (* h5 h5 h5) (* 
j2 j2 j2)) (* 3 h1 (* h2 h2) (* h5 h5 h5) (* j2 j2)) (* 3 h1 (* h2 h2) (* h5 h5 
h5) j2) (* h1 (* h2 h2) (* h5 h5 h5)) (* 7 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2 j2
)) (* 18 h1 (* h2 h2) (* h5 h5) h6 (* j2 j2)) (* 15 h1 (* h2 h2) (* h5 h5) h6 j2
) (* 4 h1 (* h2 h2) (* h5 h5) h6) (* 7 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2 j2)) 
(* 18 h1 (* h2 h2) h5 (* h6 h6) (* j2 j2)) (* 15 h1 (* h2 h2) h5 (* h6 h6) j2) 
(* 4 h1 (* h2 h2) h5 (* h6 h6)) (* h1 (* h2 h2) (* h6 h6 h6) (* j2 j2 j2)) (* 2 
h1 (* h2 h2) (* h6 h6 h6) (* j2 j2)) (* h1 (* h2 h2) (* h6 h6 h6) j2) (* 32 h1 
h2 (* h3 h3 h3) h4 (* j2 j2 j2)) (* 76 h1 h2 (* h3 h3 h3) h4 (* j2 j2)) (* 54 h1
 h2 (* h3 h3 h3) h4 j2) (* 10 h1 h2 (* h3 h3 h3) h4) (* 16 h1 h2 (* h3 h3 h3) h5
 (* j2 j2 j2 j2)) (* 78 h1 h2 (* h3 h3 h3) h5 (* j2 j2 j2)) (* 104 h1 h2 (* h3 
h3 h3) h5 (* j2 j2)) (* 50 h1 h2 (* h3 h3 h3) h5 j2) (* 8 h1 h2 (* h3 h3 h3) h5)
 (* 32 h1 h2 (* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 116 h1 h2 (* h3 h3 h3) h6 (* j2
 j2 j2)) (* 152 h1 h2 (* h3 h3 h3) h6 (* j2 j2)) (* 84 h1 h2 (* h3 h3 h3) h6 j2)
 (* 16 h1 h2 (* h3 h3 h3) h6) (* 28 h1 h2 (* h3 h3) (* h4 h4) (* j2 j2)) (* 44 
h1 h2 (* h3 h3) (* h4 h4) j2) (* 17 h1 h2 (* h3 h3) (* h4 h4)) (* 56 h1 h2 (* h3
 h3) h4 h5 (* j2 j2 j2)) (* 174 h1 h2 (* h3 h3) h4 h5 (* j2 j2)) (* 170 h1 h2 
(* h3 h3) h4 h5 j2) (* 49 h1 h2 (* h3 h3) h4 h5) (* 64 h1 h2 (* h3 h3) h4 h6 (* 
j2 j2 j2)) (* 184 h1 h2 (* h3 h3) h4 h6 (* j2 j2)) (* 155 h1 h2 (* h3 h3) h4 h6 
j2) (* 39 h1 h2 (* h3 h3) h4 h6) (* 16 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)
) (* 86 h1 h2 (* h3 h3) (* h5 h5) (* j2 j2 j2)) (* 142 h1 h2 (* h3 h3) (* h5 h5)
 (* j2 j2)) (* 87 h1 h2 (* h3 h3) (* h5 h5) j2) (* 18 h1 h2 (* h3 h3) (* h5 h5))
 (* 64 h1 h2 (* h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 241 h1 h2 (* h3 h3) h5 h6 (* j2
 j2 j2)) (* 348 h1 h2 (* h3 h3) h5 h6 (* j2 j2)) (* 219 h1 h2 (* h3 h3) h5 h6 j2
) (* 48 h1 h2 (* h3 h3) h5 h6) (* 32 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) 
(* 126 h1 h2 (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 178 h1 h2 (* h3 h3) (* h6 h6) 
(* j2 j2)) (* 106 h1 h2 (* h3 h3) (* h6 h6) j2) (* 22 h1 h2 (* h3 h3) (* h6 h6))
 (* 4 h1 h2 h3 (* h4 h4 h4) j2) (* 4 h1 h2 h3 (* h4 h4 h4)) (* 28 h1 h2 h3 (* h4
 h4) h5 (* j2 j2)) (* 56 h1 h2 h3 (* h4 h4) h5 j2) (* 23 h1 h2 h3 (* h4 h4) h5) 
(* 28 h1 h2 h3 (* h4 h4) h6 (* j2 j2)) (* 41 h1 h2 h3 (* h4 h4) h6 j2) (* 13 h1 
h2 h3 (* h4 h4) h6) (* 28 h1 h2 h3 h4 (* h5 h5) (* j2 j2 j2)) (* 87 h1 h2 h3 h4 
(* h5 h5) (* j2 j2)) (* 80 h1 h2 h3 h4 (* h5 h5) j2) (* 23 h1 h2 h3 h4 (* h5 h5)
) (* 68 h1 h2 h3 h4 h5 h6 (* j2 j2 j2)) (* 185 h1 h2 h3 h4 h5 h6 (* j2 j2)) (* 
172 h1 h2 h3 h4 h5 h6 j2) (* 46 h1 h2 h3 h4 h5 h6) (* 32 h1 h2 h3 h4 (* h6 h6) 
(* j2 j2 j2)) (* 81 h1 h2 h3 h4 (* h6 h6) (* j2 j2)) (* 62 h1 h2 h3 h4 (* h6 h6)
 j2) (* 14 h1 h2 h3 h4 (* h6 h6)) (* 4 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2 j2)) 
(* 21 h1 h2 h3 (* h5 h5 h5) (* j2 j2 j2)) (* 35 h1 h2 h3 (* h5 h5 h5) (* j2 j2))
 (* 23 h1 h2 h3 (* h5 h5 h5) j2) (* 5 h1 h2 h3 (* h5 h5 h5)) (* 32 h1 h2 h3 (* 
h5 h5) h6 (* j2 j2 j2 j2)) (* 120 h1 h2 h3 (* h5 h5) h6 (* j2 j2 j2)) (* 165 h1 
h2 h3 (* h5 h5) h6 (* j2 j2)) (* 98 h1 h2 h3 (* h5 h5) h6 j2) (* 21 h1 h2 h3 (* 
h5 h5) h6) (* 36 h1 h2 h3 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 127 h1 h2 h3 h5 (* h6
 h6) (* j2 j2 j2)) (* 174 h1 h2 h3 h5 (* h6 h6) (* j2 j2)) (* 106 h1 h2 h3 h5 
(* h6 h6) j2) (* 23 h1 h2 h3 h5 (* h6 h6)) (* 8 h1 h2 h3 (* h6 h6 h6) (* j2 j2 
j2 j2)) (* 30 h1 h2 h3 (* h6 h6 h6) (* j2 j2 j2)) (* 41 h1 h2 h3 (* h6 h6 h6) 
(* j2 j2)) (* 24 h1 h2 h3 (* h6 h6 h6) j2) (* 5 h1 h2 h3 (* h6 h6 h6)) (* 2 h1 
h2 (* h4 h4 h4) h5 j2) (* h1 h2 (* h4 h4 h4) h5) (* 2 h1 h2 (* h4 h4 h4) h6 j2) 
(* 7 h1 h2 (* h4 h4) (* h5 h5) (* j2 j2)) (* 12 h1 h2 (* h4 h4) (* h5 h5) j2) 
(* 5 h1 h2 (* h4 h4) (* h5 h5)) (* 14 h1 h2 (* h4 h4) h5 h6 (* j2 j2)) (* 19 h1 
h2 (* h4 h4) h5 h6 j2) (* 3 h1 h2 (* h4 h4) h5 h6) (* 7 h1 h2 (* h4 h4) (* h6 h6
) (* j2 j2)) (* 4 h1 h2 (* h4 h4) (* h6 h6) j2) (* 4 h1 h2 h4 (* h5 h5 h5) (* j2
 j2 j2)) (* 10 h1 h2 h4 (* h5 h5 h5) (* j2 j2)) (* 8 h1 h2 h4 (* h5 h5 h5) j2) 
(* 2 h1 h2 h4 (* h5 h5 h5)) (* 16 h1 h2 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 41 h1 
h2 h4 (* h5 h5) h6 (* j2 j2)) (* 34 h1 h2 h4 (* h5 h5) h6 j2) (* 9 h1 h2 h4 (* 
h5 h5) h6) (* 16 h1 h2 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 36 h1 h2 h4 h5 (* h6 h6)
 (* j2 j2)) (* 23 h1 h2 h4 h5 (* h6 h6) j2) (* 3 h1 h2 h4 h5 (* h6 h6)) (* 4 h1 
h2 h4 (* h6 h6 h6) (* j2 j2 j2)) (* 6 h1 h2 h4 (* h6 h6 h6) (* j2 j2)) (* 2 h1 
h2 h4 (* h6 h6 h6) j2) (* 4 h1 h2 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 14 h1 h2 
(* h5 h5 h5) h6 (* j2 j2 j2)) (* 18 h1 h2 (* h5 h5 h5) h6 (* j2 j2)) (* 10 h1 h2
 (* h5 h5 h5) h6 j2) (* 2 h1 h2 (* h5 h5 h5) h6) (* 8 h1 h2 (* h5 h5) (* h6 h6) 
(* j2 j2 j2 j2)) (* 28 h1 h2 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 36 h1 h2 (* h5
 h5) (* h6 h6) (* j2 j2)) (* 20 h1 h2 (* h5 h5) (* h6 h6) j2) (* 4 h1 h2 (* h5 
h5) (* h6 h6)) (* 4 h1 h2 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 13 h1 h2 h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 15 h1 h2 h5 (* h6 h6 h6) (* j2 j2)) (* 7 h1 h2 h5 (* h6 
h6 h6) j2) (* h1 h2 h5 (* h6 h6 h6)) (* 8 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2)
) (* 28 h1 (* h3 h3 h3) (* h4 h4) (* j2 j2)) (* 32 h1 (* h3 h3 h3) (* h4 h4) j2)
 (* 12 h1 (* h3 h3 h3) (* h4 h4)) (* 16 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) 
(* 98 h1 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 182 h1 (* h3 h3 h3) h4 h5 (* j2 j2)
) (* 132 h1 (* h3 h3 h3) h4 h5 j2) (* 32 h1 (* h3 h3 h3) h4 h5) (* 32 h1 (* h3 
h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 108 h1 (* h3 h3 h3) h4 h6 (* j2 j2 j2)) (* 140 
h1 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 84 h1 (* h3 h3 h3) h4 h6 j2) (* 20 h1 (* h3 
h3 h3) h4 h6) (* 4 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2 j2)) (* 34 h1 (* h3 
h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 98 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2)) 
(* 112 h1 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 52 h1 (* h3 h3 h3) (* h5 h5) j2) 
(* 8 h1 (* h3 h3 h3) (* h5 h5)) (* 16 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2 j2)) 
(* 104 h1 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 244 h1 (* h3 h3 h3) h5 h6 (* j2
 j2 j2)) (* 264 h1 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 132 h1 (* h3 h3 h3) h5 h6 j2
) (* 24 h1 (* h3 h3 h3) h5 h6) (* 16 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2 j2
)) (* 72 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 128 h1 (* h3 h3 h3) (* h6
 h6) (* j2 j2 j2)) (* 112 h1 (* h3 h3 h3) (* h6 h6) (* j2 j2)) (* 48 h1 (* h3 h3
 h3) (* h6 h6) j2) (* 8 h1 (* h3 h3 h3) (* h6 h6)) (* 4 h1 (* h3 h3) (* h4 h4 h4
) (* j2 j2)) (* 10 h1 (* h3 h3) (* h4 h4 h4) j2) (* 6 h1 (* h3 h3) (* h4 h4 h4))
 (* 20 h1 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 77 h1 (* h3 h3) (* h4 h4) h5 
(* j2 j2)) (* 82 h1 (* h3 h3) (* h4 h4) h5 j2) (* 26 h1 (* h3 h3) (* h4 h4) h5) 
(* 28 h1 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 64 h1 (* h3 h3) (* h4 h4) h6 
(* j2 j2)) (* 54 h1 (* h3 h3) (* h4 h4) h6 j2) (* 16 h1 (* h3 h3) (* h4 h4) h6) 
(* 16 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 94 h1 (* h3 h3) h4 (* h5 h5)
 (* j2 j2 j2)) (* 163 h1 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 112 h1 (* h3 h3) 
h4 (* h5 h5) j2) (* 26 h1 (* h3 h3) h4 (* h5 h5)) (* 64 h1 (* h3 h3) h4 h5 h6 
(* j2 j2 j2 j2)) (* 235 h1 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 345 h1 (* h3 h3) 
h4 h5 h6 (* j2 j2)) (* 220 h1 (* h3 h3) h4 h5 h6 j2) (* 50 h1 (* h3 h3) h4 h5 h6
) (* 32 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 106 h1 (* h3 h3) h4 (* h6 
h6) (* j2 j2 j2)) (* 128 h1 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 68 h1 (* h3 h3)
 h4 (* h6 h6) j2) (* 14 h1 (* h3 h3) h4 (* h6 h6)) (* 2 h1 (* h3 h3) (* h5 h5 h5
) (* j2 j2 j2 j2 j2)) (* 17 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 49 h1 
(* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 56 h1 (* h3 h3) (* h5 h5 h5) (* j2 j2)) 
(* 26 h1 (* h3 h3) (* h5 h5 h5) j2) (* 4 h1 (* h3 h3) (* h5 h5 h5)) (* 18 h1 (* 
h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 113 h1 (* h3 h3) (* h5 h5) h6 (* j2 
j2 j2 j2)) (* 249 h1 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 260 h1 (* h3 h3) 
(* h5 h5) h6 (* j2 j2)) (* 130 h1 (* h3 h3) (* h5 h5) h6 j2) (* 24 h1 (* h3 h3) 
(* h5 h5) h6) (* 32 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 144 h1 (* 
h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 274 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2 
j2)) (* 268 h1 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 130 h1 (* h3 h3) h5 (* h6 h6
) j2) (* 24 h1 (* h3 h3) h5 (* h6 h6)) (* 8 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 
j2 j2 j2)) (* 36 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 64 h1 (* h3 h3) 
(* h6 h6 h6) (* j2 j2 j2)) (* 56 h1 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 24 h1 
(* h3 h3) (* h6 h6 h6) j2) (* 4 h1 (* h3 h3) (* h6 h6 h6)) (* 4 h1 h3 (* h4 h4 
h4) h5 (* j2 j2)) (* 8 h1 h3 (* h4 h4 h4) h5 j2) (* 4 h1 h3 (* h4 h4 h4) h5) (* 
4 h1 h3 (* h4 h4 h4) h6 (* j2 j2)) (* 4 h1 h3 (* h4 h4 h4) h6 j2) (* 10 h1 h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 36 h1 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 
37 h1 h3 (* h4 h4) (* h5 h5) j2) (* 11 h1 h3 (* h4 h4) (* h5 h5)) (* 32 h1 h3 
(* h4 h4) h5 h6 (* j2 j2 j2)) (* 71 h1 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 51 h1 h3
 (* h4 h4) h5 h6 j2) (* 12 h1 h3 (* h4 h4) h5 h6) (* 14 h1 h3 (* h4 h4) (* h6 h6
) (* j2 j2 j2)) (* 20 h1 h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 7 h1 h3 (* h4 h4) 
(* h6 h6) j2) (* 4 h1 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 22 h1 h3 h4 (* h5 
h5 h5) (* j2 j2 j2)) (* 33 h1 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 18 h1 h3 h4 (* h5
 h5 h5) j2) (* 3 h1 h3 h4 (* h5 h5 h5)) (* 32 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 113 h1 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 160 h1 h3 h4 (* h5 h5) h6 (* 
j2 j2)) (* 100 h1 h3 h4 (* h5 h5) h6 j2) (* 21 h1 h3 h4 (* h5 h5) h6) (* 36 h1 
h3 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 115 h1 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) 
(* 135 h1 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 68 h1 h3 h4 h5 (* h6 h6) j2) (* 12 h1
 h3 h4 h5 (* h6 h6)) (* 8 h1 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 18 h1 h3 h4 
(* h6 h6 h6) (* j2 j2 j2)) (* 13 h1 h3 h4 (* h6 h6 h6) (* j2 j2)) (* 3 h1 h3 h4 
(* h6 h6 h6) j2) (* 4 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 26 h1 h3 (* 
h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 57 h1 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 56 h1
 h3 (* h5 h5 h5) h6 (* j2 j2)) (* 25 h1 h3 (* h5 h5 h5) h6 j2) (* 4 h1 h3 (* h5 
h5 h5) h6) (* 16 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 72 h1 h3 (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 133 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) 
(* 124 h1 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 57 h1 h3 (* h5 h5) (* h6 h6) j2) 
(* 10 h1 h3 (* h5 h5) (* h6 h6)) (* 8 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) 
(* 36 h1 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 64 h1 h3 h5 (* h6 h6 h6) (* j2 
j2 j2)) (* 56 h1 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 24 h1 h3 h5 (* h6 h6 h6) j2) 
(* 4 h1 h3 h5 (* h6 h6 h6)) (* h1 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* h1 (* h4 
h4 h4) (* h5 h5) j2) (* 2 h1 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 2 h1 (* h4 h4 h4) 
h5 h6 j2) (* h1 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* h1 (* h4 h4) (* h5 h5 h5) 
(* j2 j2 j2)) (* 2 h1 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* h1 (* h4 h4) (* h5 h5
 h5) j2) (* 7 h1 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 17 h1 (* h4 h4) (* h5 
h5) h6 (* j2 j2)) (* 11 h1 (* h4 h4) (* h5 h5) h6 j2) (* h1 (* h4 h4) (* h5 h5) 
h6) (* 7 h1 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2)) (* 12 h1 (* h4 h4) h5 (* h6 h6)
 (* j2 j2)) (* 5 h1 (* h4 h4) h5 (* h6 h6) j2) (* h1 (* h4 h4) (* h6 h6 h6) (* 
j2 j2 j2)) (* h1 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 4 h1 h4 (* h5 h5 h5) h6 
(* j2 j2 j2 j2)) (* 13 h1 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 15 h1 h4 (* h5 h5 
h5) h6 (* j2 j2)) (* 7 h1 h4 (* h5 h5 h5) h6 j2) (* h1 h4 (* h5 h5 h5) h6) (* 8 
h1 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 27 h1 h4 (* h5 h5) (* h6 h6) (* j2
 j2 j2)) (* 32 h1 h4 (* h5 h5) (* h6 h6) (* j2 j2)) (* 15 h1 h4 (* h5 h5) (* h6 
h6) j2) (* 2 h1 h4 (* h5 h5) (* h6 h6)) (* 4 h1 h4 h5 (* h6 h6 h6) (* j2 j2 j2 
j2)) (* 11 h1 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 10 h1 h4 h5 (* h6 h6 h6) (* j2
 j2)) (* 3 h1 h4 h5 (* h6 h6 h6) j2) (* 2 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 
j2 j2)) (* 9 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 16 h1 (* h5 h5 h5) 
(* h6 h6) (* j2 j2 j2)) (* 14 h1 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 6 h1 (* h5
 h5 h5) (* h6 h6) j2) (* h1 (* h5 h5 h5) (* h6 h6)) (* 2 h1 (* h5 h5) (* h6 h6 
h6) (* j2 j2 j2 j2 j2)) (* 9 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 16 h1
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 14 h1 (* h5 h5) (* h6 h6 h6) (* j2 j2))
 (* 6 h1 (* h5 h5) (* h6 h6 h6) j2) (* h1 (* h5 h5) (* h6 h6 h6)) (* 4 (* h2 h2 
h2) (* h3 h3) h4 (* j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3) h4 j2) (* (* h2 h2 h2) 
(* h3 h3) h4) (* 2 (* h2 h2 h2) (* h3 h3) h5 (* j2 j2 j2)) (* 5 (* h2 h2 h2) (* 
h3 h3) h5 (* j2 j2)) (* 4 (* h2 h2 h2) (* h3 h3) h5 j2) (* (* h2 h2 h2) (* h3 h3
) h5) (* 4 (* h2 h2 h2) (* h3 h3) h6 (* j2 j2 j2)) (* 8 (* h2 h2 h2) (* h3 h3) 
h6 (* j2 j2)) (* 5 (* h2 h2 h2) (* h3 h3) h6 j2) (* (* h2 h2 h2) (* h3 h3) h6) 
(* 2 (* h2 h2 h2) h3 (* h4 h4) j2) (* (* h2 h2 h2) h3 (* h4 h4)) (* 4 (* h2 h2 
h2) h3 h4 h5 (* j2 j2)) (* 6 (* h2 h2 h2) h3 h4 h5 j2) (* 2 (* h2 h2 h2) h3 h4 
h5) (* 4 (* h2 h2 h2) h3 h4 h6 (* j2 j2)) (* 7 (* h2 h2 h2) h3 h4 h6 j2) (* 2 
(* h2 h2 h2) h3 h4 h6) (* (* h2 h2 h2) h3 (* h5 h5) (* j2 j2 j2)) (* 3 (* h2 h2 
h2) h3 (* h5 h5) (* j2 j2)) (* 3 (* h2 h2 h2) h3 (* h5 h5) j2) (* (* h2 h2 h2) 
h3 (* h5 h5)) (* 5 (* h2 h2 h2) h3 h5 h6 (* j2 j2 j2)) (* 11 (* h2 h2 h2) h3 h5 
h6 (* j2 j2)) (* 8 (* h2 h2 h2) h3 h5 h6 j2) (* 2 (* h2 h2 h2) h3 h5 h6) (* 2 
(* h2 h2 h2) h3 (* h6 h6) (* j2 j2 j2)) (* 5 (* h2 h2 h2) h3 (* h6 h6) (* j2 j2)
) (* 4 (* h2 h2 h2) h3 (* h6 h6) j2) (* (* h2 h2 h2) h3 (* h6 h6)) (* (* h2 h2 
h2) (* h4 h4) h5 j2) (* (* h2 h2 h2) (* h4 h4) h5) (* (* h2 h2 h2) (* h4 h4) h6 
j2) (* (* h2 h2 h2) h4 (* h5 h5) (* j2 j2)) (* 2 (* h2 h2 h2) h4 (* h5 h5) j2) 
(* (* h2 h2 h2) h4 (* h5 h5)) (* 2 (* h2 h2 h2) h4 h5 h6 (* j2 j2)) (* 4 (* h2 
h2 h2) h4 h5 h6 j2) (* 2 (* h2 h2 h2) h4 h5 h6) (* (* h2 h2 h2) h4 (* h6 h6) (* 
j2 j2)) (* (* h2 h2 h2) h4 (* h6 h6) j2) (* (* h2 h2 h2) (* h5 h5) h6 (* j2 j2 
j2)) (* 3 (* h2 h2 h2) (* h5 h5) h6 (* j2 j2)) (* 3 (* h2 h2 h2) (* h5 h5) h6 j2
) (* (* h2 h2 h2) (* h5 h5) h6) (* (* h2 h2 h2) h5 (* h6 h6) (* j2 j2 j2)) (* 3 
(* h2 h2 h2) h5 (* h6 h6) (* j2 j2)) (* 3 (* h2 h2 h2) h5 (* h6 h6) j2) (* (* h2
 h2 h2) h5 (* h6 h6)) (* 8 (* h2 h2) (* h3 h3 h3) h4 (* j2 j2 j2)) (* 16 (* h2 
h2) (* h3 h3 h3) h4 (* j2 j2)) (* 10 (* h2 h2) (* h3 h3 h3) h4 j2) (* 2 (* h2 h2
) (* h3 h3 h3) h4) (* 4 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2 j2 j2)) (* 14 (* h2 
h2) (* h3 h3 h3) h5 (* j2 j2 j2)) (* 18 (* h2 h2) (* h3 h3 h3) h5 (* j2 j2)) (* 
10 (* h2 h2) (* h3 h3 h3) h5 j2) (* 2 (* h2 h2) (* h3 h3 h3) h5) (* 8 (* h2 h2) 
(* h3 h3 h3) h6 (* j2 j2 j2 j2)) (* 24 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2 j2)) 
(* 26 (* h2 h2) (* h3 h3 h3) h6 (* j2 j2)) (* 12 (* h2 h2) (* h3 h3 h3) h6 j2) 
(* 2 (* h2 h2) (* h3 h3 h3) h6) (* 8 (* h2 h2) (* h3 h3) (* h4 h4) (* j2 j2)) 
(* 12 (* h2 h2) (* h3 h3) (* h4 h4) j2) (* 4 (* h2 h2) (* h3 h3) (* h4 h4)) (* 
14 (* h2 h2) (* h3 h3) h4 h5 (* j2 j2 j2)) (* 41 (* h2 h2) (* h3 h3) h4 h5 (* j2
 j2)) (* 33 (* h2 h2) (* h3 h3) h4 h5 j2) (* 8 (* h2 h2) (* h3 h3) h4 h5) (* 16 
(* h2 h2) (* h3 h3) h4 h6 (* j2 j2 j2)) (* 42 (* h2 h2) (* h3 h3) h4 h6 (* j2 j2
)) (* 35 (* h2 h2) (* h3 h3) h4 h6 j2) (* 8 (* h2 h2) (* h3 h3) h4 h6) (* 4 (* 
h2 h2) (* h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 17 (* h2 h2) (* h3 h3) (* h5 h5) 
(* j2 j2 j2)) (* 26 (* h2 h2) (* h3 h3) (* h5 h5) (* j2 j2)) (* 17 (* h2 h2) (* 
h3 h3) (* h5 h5) j2) (* 4 (* h2 h2) (* h3 h3) (* h5 h5)) (* 16 (* h2 h2) (* h3 
h3) h5 h6 (* j2 j2 j2 j2)) (* 60 (* h2 h2) (* h3 h3) h5 h6 (* j2 j2 j2)) (* 77 
(* h2 h2) (* h3 h3) h5 h6 (* j2 j2)) (* 41 (* h2 h2) (* h3 h3) h5 h6 j2) (* 8 
(* h2 h2) (* h3 h3) h5 h6) (* 8 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2 j2)) 
(* 28 (* h2 h2) (* h3 h3) (* h6 h6) (* j2 j2 j2)) (* 36 (* h2 h2) (* h3 h3) (* 
h6 h6) (* j2 j2)) (* 20 (* h2 h2) (* h3 h3) (* h6 h6) j2) (* 4 (* h2 h2) (* h3 
h3) (* h6 h6)) (* 2 (* h2 h2) h3 (* h4 h4 h4) j2) (* (* h2 h2) h3 (* h4 h4 h4)) 
(* 8 (* h2 h2) h3 (* h4 h4) h5 (* j2 j2)) (* 16 (* h2 h2) h3 (* h4 h4) h5 j2) 
(* 7 (* h2 h2) h3 (* h4 h4) h5) (* 8 (* h2 h2) h3 (* h4 h4) h6 (* j2 j2)) (* 14 
(* h2 h2) h3 (* h4 h4) h6 j2) (* 3 (* h2 h2) h3 (* h4 h4) h6) (* 7 (* h2 h2) h3 
h4 (* h5 h5) (* j2 j2 j2)) (* 23 (* h2 h2) h3 h4 (* h5 h5) (* j2 j2)) (* 23 (* 
h2 h2) h3 h4 (* h5 h5) j2) (* 7 (* h2 h2) h3 h4 (* h5 h5)) (* 17 (* h2 h2) h3 h4
 h5 h6 (* j2 j2 j2)) (* 50 (* h2 h2) h3 h4 h5 h6 (* j2 j2)) (* 47 (* h2 h2) h3 
h4 h5 h6 j2) (* 14 (* h2 h2) h3 h4 h5 h6) (* 8 (* h2 h2) h3 h4 (* h6 h6) (* j2 
j2 j2)) (* 22 (* h2 h2) h3 h4 (* h6 h6) (* j2 j2)) (* 17 (* h2 h2) h3 h4 (* h6 
h6) j2) (* 3 (* h2 h2) h3 h4 (* h6 h6)) (* (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2
 j2)) (* 4 (* h2 h2) h3 (* h5 h5 h5) (* j2 j2 j2)) (* 6 (* h2 h2) h3 (* h5 h5 h5
) (* j2 j2)) (* 4 (* h2 h2) h3 (* h5 h5 h5) j2) (* (* h2 h2) h3 (* h5 h5 h5)) 
(* 8 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 32 (* h2 h2) h3 (* h5 h5) h6 
(* j2 j2 j2)) (* 47 (* h2 h2) h3 (* h5 h5) h6 (* j2 j2)) (* 30 (* h2 h2) h3 (* 
h5 h5) h6 j2) (* 7 (* h2 h2) h3 (* h5 h5) h6) (* 9 (* h2 h2) h3 h5 (* h6 h6) (* 
j2 j2 j2 j2)) (* 34 (* h2 h2) h3 h5 (* h6 h6) (* j2 j2 j2)) (* 48 (* h2 h2) h3 
h5 (* h6 h6) (* j2 j2)) (* 30 (* h2 h2) h3 h5 (* h6 h6) j2) (* 7 (* h2 h2) h3 h5
 (* h6 h6)) (* 2 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 7 (* h2 h2) h3 
(* h6 h6 h6) (* j2 j2 j2)) (* 9 (* h2 h2) h3 (* h6 h6 h6) (* j2 j2)) (* 5 (* h2 
h2) h3 (* h6 h6 h6) j2) (* (* h2 h2) h3 (* h6 h6 h6)) (* (* h2 h2) (* h4 h4 h4) 
h5 j2) (* (* h2 h2) (* h4 h4 h4) h5) (* (* h2 h2) (* h4 h4 h4) h6 j2) (* 2 (* h2
 h2) (* h4 h4) (* h5 h5) (* j2 j2)) (* 4 (* h2 h2) (* h4 h4) (* h5 h5) j2) (* 2 
(* h2 h2) (* h4 h4) (* h5 h5)) (* 4 (* h2 h2) (* h4 h4) h5 h6 (* j2 j2)) (* 7 
(* h2 h2) (* h4 h4) h5 h6 j2) (* 3 (* h2 h2) (* h4 h4) h5 h6) (* 2 (* h2 h2) (* 
h4 h4) (* h6 h6) (* j2 j2)) (* 2 (* h2 h2) (* h4 h4) (* h6 h6) j2) (* (* h2 h2) 
h4 (* h5 h5 h5) (* j2 j2 j2)) (* 3 (* h2 h2) h4 (* h5 h5 h5) (* j2 j2)) (* 3 (* 
h2 h2) h4 (* h5 h5 h5) j2) (* (* h2 h2) h4 (* h5 h5 h5)) (* 4 (* h2 h2) h4 (* h5
 h5) h6 (* j2 j2 j2)) (* 12 (* h2 h2) h4 (* h5 h5) h6 (* j2 j2)) (* 12 (* h2 h2)
 h4 (* h5 h5) h6 j2) (* 4 (* h2 h2) h4 (* h5 h5) h6) (* 4 (* h2 h2) h4 h5 (* h6 
h6) (* j2 j2 j2)) (* 11 (* h2 h2) h4 h5 (* h6 h6) (* j2 j2)) (* 10 (* h2 h2) h4 
h5 (* h6 h6) j2) (* 3 (* h2 h2) h4 h5 (* h6 h6)) (* (* h2 h2) h4 (* h6 h6 h6) 
(* j2 j2 j2)) (* 2 (* h2 h2) h4 (* h6 h6 h6) (* j2 j2)) (* (* h2 h2) h4 (* h6 h6
 h6) j2) (* (* h2 h2) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 4 (* h2 h2) (* h5 h5 
h5) h6 (* j2 j2 j2)) (* 6 (* h2 h2) (* h5 h5 h5) h6 (* j2 j2)) (* 4 (* h2 h2) 
(* h5 h5 h5) h6 j2) (* (* h2 h2) (* h5 h5 h5) h6) (* 2 (* h2 h2) (* h5 h5) (* h6
 h6) (* j2 j2 j2 j2)) (* 8 (* h2 h2) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 12 (* 
h2 h2) (* h5 h5) (* h6 h6) (* j2 j2)) (* 8 (* h2 h2) (* h5 h5) (* h6 h6) j2) (* 
2 (* h2 h2) (* h5 h5) (* h6 h6)) (* (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) 
(* 4 (* h2 h2) h5 (* h6 h6 h6) (* j2 j2 j2)) (* 6 (* h2 h2) h5 (* h6 h6 h6) (* 
j2 j2)) (* 4 (* h2 h2) h5 (* h6 h6 h6) j2) (* (* h2 h2) h5 (* h6 h6 h6)) (* 8 h2
 (* h3 h3 h3) (* h4 h4) (* j2 j2 j2)) (* 20 h2 (* h3 h3 h3) (* h4 h4) (* j2 j2))
 (* 16 h2 (* h3 h3 h3) (* h4 h4) j2) (* 4 h2 (* h3 h3 h3) (* h4 h4)) (* 8 h2 (* 
h3 h3 h3) h4 h5 (* j2 j2 j2 j2)) (* 44 h2 (* h3 h3 h3) h4 h5 (* j2 j2 j2)) (* 68
 h2 (* h3 h3 h3) h4 h5 (* j2 j2)) (* 40 h2 (* h3 h3 h3) h4 h5 j2) (* 8 h2 (* h3 
h3 h3) h4 h5) (* 16 h2 (* h3 h3 h3) h4 h6 (* j2 j2 j2 j2)) (* 56 h2 (* h3 h3 h3)
 h4 h6 (* j2 j2 j2)) (* 74 h2 (* h3 h3 h3) h4 h6 (* j2 j2)) (* 42 h2 (* h3 h3 h3
) h4 h6 j2) (* 8 h2 (* h3 h3 h3) h4 h6) (* 2 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 
j2 j2 j2)) (* 14 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2 j2 j2)) (* 34 h2 (* h3 h3 h3
) (* h5 h5) (* j2 j2 j2)) (* 38 h2 (* h3 h3 h3) (* h5 h5) (* j2 j2)) (* 20 h2 
(* h3 h3 h3) (* h5 h5) j2) (* 4 h2 (* h3 h3 h3) (* h5 h5)) (* 8 h2 (* h3 h3 h3) 
h5 h6 (* j2 j2 j2 j2 j2)) (* 54 h2 (* h3 h3 h3) h5 h6 (* j2 j2 j2 j2)) (* 116 h2
 (* h3 h3 h3) h5 h6 (* j2 j2 j2)) (* 110 h2 (* h3 h3 h3) h5 h6 (* j2 j2)) (* 48 
h2 (* h3 h3 h3) h5 h6 j2) (* 8 h2 (* h3 h3 h3) h5 h6) (* 8 h2 (* h3 h3 h3) (* h6
 h6) (* j2 j2 j2 j2 j2)) (* 36 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2 j2)) (* 64 
h2 (* h3 h3 h3) (* h6 h6) (* j2 j2 j2)) (* 56 h2 (* h3 h3 h3) (* h6 h6) (* j2 j2
)) (* 24 h2 (* h3 h3 h3) (* h6 h6) j2) (* 4 h2 (* h3 h3 h3) (* h6 h6)) (* 4 h2 
(* h3 h3) (* h4 h4 h4) (* j2 j2)) (* 6 h2 (* h3 h3) (* h4 h4 h4) j2) (* 2 h2 (* 
h3 h3) (* h4 h4 h4)) (* 14 h2 (* h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 46 h2 (* 
h3 h3) (* h4 h4) h5 (* j2 j2)) (* 46 h2 (* h3 h3) (* h4 h4) h5 j2) (* 14 h2 (* 
h3 h3) (* h4 h4) h5) (* 16 h2 (* h3 h3) (* h4 h4) h6 (* j2 j2 j2)) (* 44 h2 (* 
h3 h3) (* h4 h4) h6 (* j2 j2)) (* 33 h2 (* h3 h3) (* h4 h4) h6 j2) (* 6 h2 (* h3
 h3) (* h4 h4) h6) (* 8 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 48 h2 (* 
h3 h3) h4 (* h5 h5) (* j2 j2 j2)) (* 87 h2 (* h3 h3) h4 (* h5 h5) (* j2 j2)) (* 
60 h2 (* h3 h3) h4 (* h5 h5) j2) (* 14 h2 (* h3 h3) h4 (* h5 h5)) (* 32 h2 (* h3
 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 130 h2 (* h3 h3) h4 h5 h6 (* j2 j2 j2)) (* 192
 h2 (* h3 h3) h4 h5 h6 (* j2 j2)) (* 123 h2 (* h3 h3) h4 h5 h6 j2) (* 28 h2 (* 
h3 h3) h4 h5 h6) (* 16 h2 (* h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 60 h2 (* h3
 h3) h4 (* h6 h6) (* j2 j2 j2)) (* 77 h2 (* h3 h3) h4 (* h6 h6) (* j2 j2)) (* 39
 h2 (* h3 h3) h4 (* h6 h6) j2) (* 6 h2 (* h3 h3) h4 (* h6 h6)) (* h2 (* h3 h3) 
(* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 7 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2 j2))
 (* 17 h2 (* h3 h3) (* h5 h5 h5) (* j2 j2 j2)) (* 19 h2 (* h3 h3) (* h5 h5 h5) 
(* j2 j2)) (* 10 h2 (* h3 h3) (* h5 h5 h5) j2) (* 2 h2 (* h3 h3) (* h5 h5 h5)) 
(* 9 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 58 h2 (* h3 h3) (* h5 h5) 
h6 (* j2 j2 j2 j2)) (* 137 h2 (* h3 h3) (* h5 h5) h6 (* j2 j2 j2)) (* 148 h2 (* 
h3 h3) (* h5 h5) h6 (* j2 j2)) (* 74 h2 (* h3 h3) (* h5 h5) h6 j2) (* 14 h2 (* 
h3 h3) (* h5 h5) h6) (* 16 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 j2)) (* 79 
h2 (* h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 156 h2 (* h3 h3) h5 (* h6 h6) (* 
j2 j2 j2)) (* 153 h2 (* h3 h3) h5 (* h6 h6) (* j2 j2)) (* 74 h2 (* h3 h3) h5 (* 
h6 h6) j2) (* 14 h2 (* h3 h3) h5 (* h6 h6)) (* 4 h2 (* h3 h3) (* h6 h6 h6) (* j2
 j2 j2 j2 j2)) (* 18 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 32 h2 (* h3 
h3) (* h6 h6 h6) (* j2 j2 j2)) (* 28 h2 (* h3 h3) (* h6 h6 h6) (* j2 j2)) (* 12 
h2 (* h3 h3) (* h6 h6 h6) j2) (* 2 h2 (* h3 h3) (* h6 h6 h6)) (* 4 h2 h3 (* h4 
h4 h4) h5 (* j2 j2)) (* 9 h2 h3 (* h4 h4 h4) h5 j2) (* 4 h2 h3 (* h4 h4 h4) h5) 
(* 4 h2 h3 (* h4 h4 h4) h6 (* j2 j2)) (* 4 h2 h3 (* h4 h4 h4) h6 j2) (* 7 h2 h3 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 24 h2 h3 (* h4 h4) (* h5 h5) (* j2 j2)) (* 
25 h2 h3 (* h4 h4) (* h5 h5) j2) (* 8 h2 h3 (* h4 h4) (* h5 h5)) (* 17 h2 h3 (* 
h4 h4) h5 h6 (* j2 j2 j2)) (* 48 h2 h3 (* h4 h4) h5 h6 (* j2 j2)) (* 45 h2 h3 
(* h4 h4) h5 h6 j2) (* 12 h2 h3 (* h4 h4) h5 h6) (* 8 h2 h3 (* h4 h4) (* h6 h6) 
(* j2 j2 j2)) (* 17 h2 h3 (* h4 h4) (* h6 h6) (* j2 j2)) (* 8 h2 h3 (* h4 h4) 
(* h6 h6) j2) (* 2 h2 h3 h4 (* h5 h5 h5) (* j2 j2 j2 j2)) (* 12 h2 h3 h4 (* h5 
h5 h5) (* j2 j2 j2)) (* 22 h2 h3 h4 (* h5 h5 h5) (* j2 j2)) (* 16 h2 h3 h4 (* h5
 h5 h5) j2) (* 4 h2 h3 h4 (* h5 h5 h5)) (* 16 h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 67 h2 h3 h4 (* h5 h5) h6 (* j2 j2 j2)) (* 102 h2 h3 h4 (* h5 h5) h6 (* 
j2 j2)) (* 67 h2 h3 h4 (* h5 h5) h6 j2) (* 16 h2 h3 h4 (* h5 h5) h6) (* 18 h2 h3
 h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 66 h2 h3 h4 h5 (* h6 h6) (* j2 j2 j2)) (* 
93 h2 h3 h4 h5 (* h6 h6) (* j2 j2)) (* 57 h2 h3 h4 h5 (* h6 h6) j2) (* 12 h2 h3 
h4 h5 (* h6 h6)) (* 4 h2 h3 h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 12 h2 h3 h4 (* 
h6 h6 h6) (* j2 j2 j2)) (* 12 h2 h3 h4 (* h6 h6 h6) (* j2 j2)) (* 4 h2 h3 h4 (* 
h6 h6 h6) j2) (* 2 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 14 h2 h3 (* h5 
h5 h5) h6 (* j2 j2 j2 j2)) (* 34 h2 h3 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 38 h2 h3
 (* h5 h5 h5) h6 (* j2 j2)) (* 20 h2 h3 (* h5 h5 h5) h6 j2) (* 4 h2 h3 (* h5 h5 
h5) h6) (* 8 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 41 h2 h3 (* h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 83 h2 h3 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 83 
h2 h3 (* h5 h5) (* h6 h6) (* j2 j2)) (* 41 h2 h3 (* h5 h5) (* h6 h6) j2) (* 8 h2
 h3 (* h5 h5) (* h6 h6)) (* 4 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 21 h2
 h3 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 43 h2 h3 h5 (* h6 h6 h6) (* j2 j2 j2)) 
(* 43 h2 h3 h5 (* h6 h6 h6) (* j2 j2)) (* 21 h2 h3 h5 (* h6 h6 h6) j2) (* 4 h2 
h3 h5 (* h6 h6 h6)) (* h2 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 2 h2 (* h4 h4 h4)
 (* h5 h5) j2) (* h2 (* h4 h4 h4) (* h5 h5)) (* 2 h2 (* h4 h4 h4) h5 h6 (* j2 j2
)) (* 2 h2 (* h4 h4 h4) h5 h6 j2) (* h2 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* h2 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2)) (* 3 h2 (* h4 h4) (* h5 h5 h5) (* j2 j2)) 
(* 3 h2 (* h4 h4) (* h5 h5 h5) j2) (* h2 (* h4 h4) (* h5 h5 h5)) (* 4 h2 (* h4 
h4) (* h5 h5) h6 (* j2 j2 j2)) (* 11 h2 (* h4 h4) (* h5 h5) h6 (* j2 j2)) (* 10 
h2 (* h4 h4) (* h5 h5) h6 j2) (* 3 h2 (* h4 h4) (* h5 h5) h6) (* 4 h2 (* h4 h4) 
h5 (* h6 h6) (* j2 j2 j2)) (* 8 h2 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 4 h2 (* 
h4 h4) h5 (* h6 h6) j2) (* h2 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2)) (* h2 (* h4 
h4) (* h6 h6 h6) (* j2 j2)) (* 2 h2 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 8 h2 
h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 12 h2 h4 (* h5 h5 h5) h6 (* j2 j2)) (* 8 h2 
h4 (* h5 h5 h5) h6 j2) (* 2 h2 h4 (* h5 h5 h5) h6) (* 4 h2 h4 (* h5 h5) (* h6 h6
) (* j2 j2 j2 j2)) (* 15 h2 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 21 h2 h4 (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 13 h2 h4 (* h5 h5) (* h6 h6) j2) (* 3 h2 h4 (* h5
 h5) (* h6 h6)) (* 2 h2 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 h2 h4 h5 (* h6 
h6 h6) (* j2 j2 j2)) (* 6 h2 h4 h5 (* h6 h6 h6) (* j2 j2)) (* 2 h2 h4 h5 (* h6 
h6 h6) j2) (* h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 5 h2 (* h5 h5 h5)
 (* h6 h6) (* j2 j2 j2 j2)) (* 10 h2 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2)) (* 10 
h2 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 5 h2 (* h5 h5 h5) (* h6 h6) j2) (* h2 
(* h5 h5 h5) (* h6 h6)) (* h2 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 5 h2
 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 10 h2 (* h5 h5) (* h6 h6 h6) (* j2 
j2 j2)) (* 10 h2 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* 5 h2 (* h5 h5) (* h6 h6 h6
) j2) (* h2 (* h5 h5) (* h6 h6 h6)) (* 4 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2 
j2)) (* 24 (* h3 h3 h3) (* h4 h4) h5 (* j2 j2 j2)) (* 44 (* h3 h3 h3) (* h4 h4) 
h5 (* j2 j2)) (* 32 (* h3 h3 h3) (* h4 h4) h5 j2) (* 8 (* h3 h3 h3) (* h4 h4) h5
) (* 8 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2 j2 j2)) (* 20 (* h3 h3 h3) (* h4 h4) 
h6 (* j2 j2 j2)) (* 16 (* h3 h3 h3) (* h4 h4) h6 (* j2 j2)) (* 4 (* h3 h3 h3) 
(* h4 h4) h6 j2) (* 2 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2 j2)) (* 18 (* h3 
h3 h3) h4 (* h5 h5) (* j2 j2 j2 j2)) (* 56 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2 j2
)) (* 72 (* h3 h3 h3) h4 (* h5 h5) (* j2 j2)) (* 40 (* h3 h3 h3) h4 (* h5 h5) j2
) (* 8 (* h3 h3 h3) h4 (* h5 h5)) (* 8 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2 j2))
 (* 58 (* h3 h3 h3) h4 h5 h6 (* j2 j2 j2 j2)) (* 138 (* h3 h3 h3) h4 h5 h6 (* j2
 j2 j2)) (* 152 (* h3 h3 h3) h4 h5 h6 (* j2 j2)) (* 80 (* h3 h3 h3) h4 h5 h6 j2)
 (* 16 (* h3 h3 h3) h4 h5 h6) (* 8 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2 j2))
 (* 28 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2 j2 j2)) (* 36 (* h3 h3 h3) h4 (* h6 h6
) (* j2 j2 j2)) (* 20 (* h3 h3 h3) h4 (* h6 h6) (* j2 j2)) (* 4 (* h3 h3 h3) h4 
(* h6 h6) j2) (* 8 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 52 (* h3 h3 
h3) (* h5 h5) h6 (* j2 j2 j2 j2)) (* 112 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2 j2))
 (* 108 (* h3 h3 h3) (* h5 h5) h6 (* j2 j2)) (* 48 (* h3 h3 h3) (* h5 h5) h6 j2)
 (* 8 (* h3 h3 h3) (* h5 h5) h6) (* 16 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2 
j2)) (* 72 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 128 (* h3 h3 h3) h5 (* 
h6 h6) (* j2 j2 j2)) (* 112 (* h3 h3 h3) h5 (* h6 h6) (* j2 j2)) (* 48 (* h3 h3 
h3) h5 (* h6 h6) j2) (* 8 (* h3 h3 h3) h5 (* h6 h6)) (* 2 (* h3 h3) (* h4 h4 h4)
 h5 (* j2 j2 j2)) (* 10 (* h3 h3) (* h4 h4 h4) h5 (* j2 j2)) (* 12 (* h3 h3) (* 
h4 h4 h4) h5 j2) (* 4 (* h3 h3) (* h4 h4 h4) h5) (* 4 (* h3 h3) (* h4 h4 h4) h6 
(* j2 j2 j2)) (* 6 (* h3 h3) (* h4 h4 h4) h6 (* j2 j2)) (* 2 (* h3 h3) (* h4 h4 
h4) h6 j2) (* 4 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2 j2 j2)) (* 24 (* h3 h3) 
(* h4 h4) (* h5 h5) (* j2 j2 j2)) (* 44 (* h3 h3) (* h4 h4) (* h5 h5) (* j2 j2))
 (* 32 (* h3 h3) (* h4 h4) (* h5 h5) j2) (* 8 (* h3 h3) (* h4 h4) (* h5 h5)) (* 
16 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2 j2 j2)) (* 57 (* h3 h3) (* h4 h4) h5 h6 
(* j2 j2 j2)) (* 84 (* h3 h3) (* h4 h4) h5 h6 (* j2 j2)) (* 54 (* h3 h3) (* h4 
h4) h5 h6 j2) (* 12 (* h3 h3) (* h4 h4) h5 h6) (* 8 (* h3 h3) (* h4 h4) (* h6 h6
) (* j2 j2 j2 j2)) (* 22 (* h3 h3) (* h4 h4) (* h6 h6) (* j2 j2 j2)) (* 17 (* h3
 h3) (* h4 h4) (* h6 h6) (* j2 j2)) (* 4 (* h3 h3) (* h4 h4) (* h6 h6) j2) (* 
(* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2 j2 j2)) (* 9 (* h3 h3) h4 (* h5 h5 h5) (* 
j2 j2 j2 j2)) (* 28 (* h3 h3) h4 (* h5 h5 h5) (* j2 j2 j2)) (* 36 (* h3 h3) h4 
(* h5 h5 h5) (* j2 j2)) (* 20 (* h3 h3) h4 (* h5 h5 h5) j2) (* 4 (* h3 h3) h4 
(* h5 h5 h5)) (* 9 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 64 (* h3 h3)
 h4 (* h5 h5) h6 (* j2 j2 j2 j2)) (* 149 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2 j2))
 (* 160 (* h3 h3) h4 (* h5 h5) h6 (* j2 j2)) (* 82 (* h3 h3) h4 (* h5 h5) h6 j2)
 (* 16 (* h3 h3) h4 (* h5 h5) h6) (* 16 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2
 j2)) (* 69 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2 j2 j2)) (* 135 (* h3 h3) h4 h5 
(* h6 h6) (* j2 j2 j2)) (* 136 (* h3 h3) h4 h5 (* h6 h6) (* j2 j2)) (* 66 (* h3 
h3) h4 h5 (* h6 h6) j2) (* 12 (* h3 h3) h4 h5 (* h6 h6)) (* 4 (* h3 h3) h4 (* h6
 h6 h6) (* j2 j2 j2 j2 j2)) (* 14 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 
18 (* h3 h3) h4 (* h6 h6 h6) (* j2 j2 j2)) (* 10 (* h3 h3) h4 (* h6 h6 h6) (* j2
 j2)) (* 2 (* h3 h3) h4 (* h6 h6 h6) j2) (* 4 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2
 j2 j2 j2)) (* 26 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2 j2 j2)) (* 56 (* h3 h3) (* 
h5 h5 h5) h6 (* j2 j2 j2)) (* 54 (* h3 h3) (* h5 h5 h5) h6 (* j2 j2)) (* 24 (* 
h3 h3) (* h5 h5 h5) h6 j2) (* 4 (* h3 h3) (* h5 h5 h5) h6) (* 20 (* h3 h3) (* h5
 h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 82 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 
j2 j2)) (* 136 (* h3 h3) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 114 (* h3 h3) (* 
h5 h5) (* h6 h6) (* j2 j2)) (* 48 (* h3 h3) (* h5 h5) (* h6 h6) j2) (* 8 (* h3 
h3) (* h5 h5) (* h6 h6)) (* 8 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 
36 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 64 (* h3 h3) h5 (* h6 h6 h6) 
(* j2 j2 j2)) (* 56 (* h3 h3) h5 (* h6 h6 h6) (* j2 j2)) (* 24 (* h3 h3) h5 (* 
h6 h6 h6) j2) (* 4 (* h3 h3) h5 (* h6 h6 h6)) (* h3 (* h4 h4 h4) (* h5 h5) (* j2
 j2 j2)) (* 5 h3 (* h4 h4 h4) (* h5 h5) (* j2 j2)) (* 6 h3 (* h4 h4 h4) (* h5 h5
) j2) (* 2 h3 (* h4 h4 h4) (* h5 h5)) (* 5 h3 (* h4 h4 h4) h5 h6 (* j2 j2 j2)) 
(* 9 h3 (* h4 h4 h4) h5 h6 (* j2 j2)) (* 4 h3 (* h4 h4 h4) h5 h6 j2) (* 2 h3 (* 
h4 h4 h4) (* h6 h6) (* j2 j2 j2)) (* h3 (* h4 h4 h4) (* h6 h6) (* j2 j2)) (* h3 
(* h4 h4) (* h5 h5 h5) (* j2 j2 j2 j2)) (* 6 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2 
j2)) (* 11 h3 (* h4 h4) (* h5 h5 h5) (* j2 j2)) (* 8 h3 (* h4 h4) (* h5 h5 h5) 
j2) (* 2 h3 (* h4 h4) (* h5 h5 h5)) (* 8 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2 
j2)) (* 29 h3 (* h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 42 h3 (* h4 h4) (* h5 h5) 
h6 (* j2 j2)) (* 27 h3 (* h4 h4) (* h5 h5) h6 j2) (* 6 h3 (* h4 h4) (* h5 h5) h6
) (* 9 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2 j2 j2)) (* 28 h3 (* h4 h4) h5 (* h6 h6
) (* j2 j2 j2)) (* 27 h3 (* h4 h4) h5 (* h6 h6) (* j2 j2)) (* 8 h3 (* h4 h4) h5 
(* h6 h6) j2) (* 2 h3 (* h4 h4) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 3 h3 (* h4 h4) 
(* h6 h6 h6) (* j2 j2 j2)) (* h3 (* h4 h4) (* h6 h6 h6) (* j2 j2)) (* 2 h3 h4 
(* h5 h5 h5) h6 (* j2 j2 j2 j2 j2)) (* 15 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2 j2))
 (* 37 h3 h4 (* h5 h5 h5) h6 (* j2 j2 j2)) (* 41 h3 h4 (* h5 h5 h5) h6 (* j2 j2)
) (* 21 h3 h4 (* h5 h5 h5) h6 j2) (* 4 h3 h4 (* h5 h5 h5) h6) (* 8 h3 h4 (* h5 
h5) (* h6 h6) (* j2 j2 j2 j2 j2)) (* 36 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2 j2
)) (* 69 h3 h4 (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 68 h3 h4 (* h5 h5) (* h6 h6)
 (* j2 j2)) (* 33 h3 h4 (* h5 h5) (* h6 h6) j2) (* 6 h3 h4 (* h5 h5) (* h6 h6)) 
(* 4 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 17 h3 h4 h5 (* h6 h6 h6) (* j2
 j2 j2 j2)) (* 26 h3 h4 h5 (* h6 h6 h6) (* j2 j2 j2)) (* 17 h3 h4 h5 (* h6 h6 h6
) (* j2 j2)) (* 4 h3 h4 h5 (* h6 h6 h6) j2) (* 4 h3 (* h5 h5 h5) (* h6 h6) (* j2
 j2 j2 j2 j2)) (* 18 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 32 h3 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 28 h3 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* 12 
h3 (* h5 h5 h5) (* h6 h6) j2) (* 2 h3 (* h5 h5 h5) (* h6 h6)) (* 4 h3 (* h5 h5) 
(* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 18 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)
) (* 32 h3 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2)) (* 28 h3 (* h5 h5) (* h6 h6 h6) 
(* j2 j2)) (* 12 h3 (* h5 h5) (* h6 h6 h6) j2) (* 2 h3 (* h5 h5) (* h6 h6 h6)) 
(* (* h4 h4 h4) (* h5 h5) h6 (* j2 j2 j2)) (* 2 (* h4 h4 h4) (* h5 h5) h6 (* j2 
j2)) (* (* h4 h4 h4) (* h5 h5) h6 j2) (* (* h4 h4 h4) h5 (* h6 h6) (* j2 j2 j2))
 (* (* h4 h4 h4) h5 (* h6 h6) (* j2 j2)) (* (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 
j2 j2)) (* 3 (* h4 h4) (* h5 h5 h5) h6 (* j2 j2 j2)) (* 3 (* h4 h4) (* h5 h5 h5)
 h6 (* j2 j2)) (* (* h4 h4) (* h5 h5 h5) h6 j2) (* 2 (* h4 h4) (* h5 h5) (* h6 
h6) (* j2 j2 j2 j2)) (* 6 (* h4 h4) (* h5 h5) (* h6 h6) (* j2 j2 j2)) (* 6 (* h4
 h4) (* h5 h5) (* h6 h6) (* j2 j2)) (* 2 (* h4 h4) (* h5 h5) (* h6 h6) j2) (* 
(* h4 h4) h5 (* h6 h6 h6) (* j2 j2 j2 j2)) (* 2 (* h4 h4) h5 (* h6 h6 h6) (* j2 
j2 j2)) (* (* h4 h4) h5 (* h6 h6 h6) (* j2 j2)) (* h4 (* h5 h5 h5) (* h6 h6) (* 
j2 j2 j2 j2 j2)) (* 4 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2 j2 j2)) (* 6 h4 (* h5 
h5 h5) (* h6 h6) (* j2 j2 j2)) (* 4 h4 (* h5 h5 h5) (* h6 h6) (* j2 j2)) (* h4 
(* h5 h5 h5) (* h6 h6) j2) (* h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2 j2)) (* 4
 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2 j2 j2)) (* 6 h4 (* h5 h5) (* h6 h6 h6) (* j2
 j2 j2)) (* 4 h4 (* h5 h5) (* h6 h6 h6) (* j2 j2)) (* h4 (* h5 h5) (* h6 h6 h6) 
j2)) 0)))
(check-sat)
(exit)
